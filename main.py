import csv

import logging

import math

import os

import re

from collections import defaultdict

from datetime import date, datetime, timedelta, timezone

from functools import lru_cache

from pathlib import Path



import requests

from dotenv import load_dotenv

from fastapi import FastAPI, HTTPException

from pydantic import BaseModel, Field



load_dotenv()

log = logging.getLogger('sap_stock')

logging.basicConfig(level=logging.INFO)

app = FastAPI(title='SAP TabPFN 7-day stock planning')

BASE = os.getenv('S4_BASE_URL', '').rstrip('/')

CLIENT = os.getenv('S4_CLIENT', '100')

VERIFY = os.getenv('VERIFY_SSL', 'true').lower() == 'true'

CSV_PATH = os.getenv('TRAINING_CSV_PATH', str(Path(__file__).with_name('stock_training_NEXT_7_DAYS_DEMO.csv')))

FEATURES = ['CurrentStock', 'Consumption30D', 'OpenPO30D', 'Demand30D']

MOVEMENTS = {'201':1, '221':1, '261':1, '281':1, '601':1,

             '202':-1, '222':-1, '262':-1, '282':-1, '602':-1}



class StockRequest(BaseModel):

    material: str = Field(min_length=1)

    plant: str = Field(min_length=1)

    as_of_date: date | None = None



def qty(v):

    if v is None or v == '':

        return 0.0

    n = float(v)

    if not math.isfinite(n):

        raise ValueError('Non-finite SAP quantity')

    return n



def sap_date(v):

    if v is None or v == '':

        return None

    if isinstance(v, datetime):

        return v.date()

    if isinstance(v, date):

        return v

    s = str(v)

    m = re.fullmatch(r'/Date\((-?\d+)(?:[+-]\d{4})?\)/', s)

    if m:

        return datetime.fromtimestamp(int(m.group(1))/1000, tz=timezone.utc).date()

    try:

        return date.fromisoformat(s[:10])

    except ValueError:

        raise ValueError(f'Unsupported SAP date: {s}')



def esc(v):

    return str(v).replace("'", "''")



def sap_get(service, entity, params=None):

    if not BASE or not os.getenv('S4_USERNAME') or not os.getenv('S4_PASSWORD'):

        raise RuntimeError('Set S4_BASE_URL, S4_USERNAME and S4_PASSWORD')

    url = f'{BASE}/sap/opu/odata/sap/{service}/{entity}'

    p = {'sap-client': CLIENT, '$format': 'json'}

    p.update(params or {})

    r = requests.get(url, params=p, auth=(os.getenv('S4_USERNAME'), os.getenv('S4_PASSWORD')),

                     headers={'Accept':'application/json'}, verify=VERIFY, timeout=60)

    r.raise_for_status()

    return r.json()['d']



def sap_rows(service, entity, filter_expr=None, page_size=200, max_rows=50000):

    # Prefer SAP server paging (__next), fall back to $skip for services using $top.

    out, skip = [], 0

    while True:

        p = {'$top':str(page_size), '$skip':str(skip)}

        if filter_expr:

            p['$filter'] = filter_expr

        d = sap_get(service, entity, p)

        batch = d.get('results', [])

        out.extend(batch)

        if len(out) > max_rows:

            raise RuntimeError(f'SAP result exceeded {max_rows} rows: {entity}')

        if not batch:

            break

        if not d.get('__next') and len(batch) < page_size:

            break

        skip += len(batch)

    return out



def nav_lines(service, item, navigation='to_ScheduleLine'):

    # Use the exact item navigation path, not filters on invalid schedule-line properties.

    data = item.get(navigation) or {}

    if 'results' in data:

        return data['results']

    uri = item.get('__metadata', {}).get('uri', '')

    if not uri:

        raise RuntimeError('Missing SAP item navigation URI')

    # Entity URI includes the correct OData key syntax.

    entity = uri.split(f'/sap/opu/odata/sap/{service}/', 1)[-1]

    return sap_rows(service, f'{entity}/{navigation}')



def window(records, as_of, kind):

    """records = [(date, quantity)]; 30 calendar days inclusive.

    Consumption: trailing 30 days; PO/sales: upcoming 30 days.

    If no records in primary window, trailing 30 days ending at latest past record.

    """

    valid = [(d, q) for d, q in records if d is not None and q > 0]

    if kind == 'consumption':

        start, end = as_of - timedelta(days=29), as_of

    else:

        start, end = as_of, as_of + timedelta(days=29)

    current = [(d, q) for d, q in valid if start <= d <= end]

    if current:

        return {'quantity':round(sum(q for _,q in current),3), 'source':'CURRENT',

                'start':str(start), 'end':str(end), 'reference_date':str(as_of)}

    # Past records are strictly before as_of; no future data can become history.

    historical = [(d,q) for d,q in valid if d < as_of]

    if historical:

        latest = max(d for d,_ in historical)

        hstart = latest - timedelta(days=29)

        return {'quantity':round(sum(q for d,q in historical if hstart <= d <= latest),3),

                'source':'HISTORICAL_FALLBACK', 'start':str(hstart), 'end':str(latest),

                'reference_date':str(latest)}

    return {'quantity':0.0, 'source':'NO_DATED_RECORDS_IN_WINDOW',

            'start':str(start), 'end':str(end), 'reference_date':None}



def safety_stock_from_sap(material, plant):

    """Plant-level configured MRP safety stock; no invented defaults."""

    key = (f"A_ProductSupplyPlanning(Product='{esc(material)}',"

           f"Plant='{esc(plant)}')")

    row = sap_get('API_PRODUCT_SRV', key)

    if 'SafetyStockQuantity' not in row or row['SafetyStockQuantity'] is None:

        raise RuntimeError('SAP product planning has no SafetyStockQuantity for this product/plant')

    configured = qty(row['SafetyStockQuantity'])

    minimum = qty(row.get('MinimumSafetyStockQuantity'))

    if configured < 0 or minimum < 0:

        raise RuntimeError('Negative safety stock in SAP product planning')

    # Use configured safety stock, respecting the maintained minimum floor.

    return {'quantity': max(configured, minimum),

            'configured': configured, 'minimum': minimum,

            'source': 'SAP_PRODUCT_SUPPLY_PLANNING',

            'product': row.get('Product', material), 'plant': row.get('Plant', plant)}



def current_stock(material, plant):

    f = f"Material eq '{esc(material)}' and Plant eq '{esc(plant)}'"

    rows = sap_rows('API_MATERIAL_STOCK_SRV','A_MatlStkInAcctMod', f)

    total, seen = 0.0, set()

    for r in rows:

        if str(r.get('InventoryStockType') or '') not in ('01','') or r.get('InventorySpecialStockType'):

            continue

        key = tuple(r.get(k) for k in ('Material','Plant','StorageLocation','Batch','InventoryStockType','InventorySpecialStockType','Supplier','Customer'))

        if key in seen:

            continue

        seen.add(key)

        total += qty(r.get('MatlWrhsStkQtyInMatlBaseUnit'))

    return max(0.0,total)



@lru_cache(maxsize=20000)

def posting_date(year, document):

    key = f"A_MaterialDocumentHeader(MaterialDocumentYear='{esc(year)}',MaterialDocument='{esc(document)}')"

    return sap_date(sap_get('API_MATERIAL_DOCUMENT_SRV',key).get('PostingDate'))



def consumption(material, plant, as_of):

    f = f"Material eq '{esc(material)}' and Plant eq '{esc(plant)}'"

    items = sap_rows('API_MATERIAL_DOCUMENT_SRV','A_MaterialDocumentItem',f)

    movements = defaultdict(float)

    for it in items:

        movement = str(it.get('GoodsMovementType') or '')

        if movement not in MOVEMENTS or it.get('GoodsMovementIsCancelled') is True:

            continue

        year, doc = it.get('MaterialDocumentYear'), it.get('MaterialDocument')

        if not year or not doc:

            continue

        d = posting_date(str(year),str(doc))

        if d is None or d > as_of:

            continue

        amount = qty(it.get('QuantityInBaseUnit')) * MOVEMENTS[movement]

        movements[d] += amount

    # Keep signed reversals inside window; never discard negative entries before summing.

    signed = list(movements.items())

    start, end = as_of-timedelta(days=29), as_of

    current = [(d,q) for d,q in signed if start <= d <= end]

    if current:

        return {'quantity':round(max(0,sum(q for _,q in current)),3), 'source':'CURRENT',

                'start':str(start), 'end':str(end), 'reference_date':str(as_of)}

    older = [(d,q) for d,q in signed if d < as_of]

    if older:

        latest = max(d for d,_ in older)

        begin = latest-timedelta(days=29)

        return {'quantity':round(max(0,sum(q for d,q in older if begin<=d<=latest)),3),

                'source':'HISTORICAL_FALLBACK','start':str(begin),'end':str(latest),

                'reference_date':str(latest)}

    return {'quantity':0,'source':'NO_HISTORY','start':str(start),'end':str(end),'reference_date':None}



def purchase_orders(material,plant,as_of):

    f = f"Material eq '{esc(material)}' and Plant eq '{esc(plant)}'"

    items = sap_rows('API_PURCHASEORDER_PROCESS_SRV','A_PurchaseOrderItem',f)

    records = []

    excluded_direct_consumption = 0

    for it in items:

        if (it.get('PurchasingDocumentDeletionCode') or it.get('IsCompletelyDelivered') or

            it.get('GoodsReceiptIsExpected') is False or it.get('IsReturnsItem')):

            continue

        # Include K for historical scheduled-PO reporting, but NEVER as verified incoming.

        if it.get('AccountAssignmentCategory'):

            excluded_direct_consumption += 1

        for line in nav_lines('API_PURCHASEORDER_PROCESS_SRV',it):

            d = sap_date(line.get('ScheduleLineDeliveryDate'))

            q = qty(line.get('ScheduleLineOrderQuantity'))

            if d and q > 0:

                records.append((d,q))

    result = window(records,as_of,'po')

    # SAP schedule-line order quantity is not the GR-adjusted outstanding quantity.

    # Keep this feature labelled as scheduled, not falsely verified open PO.

    result['quantity_basis'] = 'SCHEDULED_NOT_GR_ADJUSTED'

    result['account_assigned_items_not_inventory_receipts'] = excluded_direct_consumption

    result['usable_as_confirmed_incoming'] = False

    return result



def sales_demand(material,plant,as_of):

    f = f"Material eq '{esc(material)}'"

    items = sap_rows('API_SALES_ORDER_SRV','A_SalesOrderItem',f)

    records = []

    for it in items:

        if str(it.get('ProductionPlant') or '') != str(plant):

            continue

        if it.get('SalesDocumentRjcnReason') or it.get('DeliveryStatus') == 'C' or it.get('SDProcessStatus') == 'C':

            continue

        lines = nav_lines('API_SALES_ORDER_SRV',it)

        requested = [(sap_date(l.get('RequestedDeliveryDate')), qty(l.get('ScheduleLineOrderQuantity')))

                     for l in lines if l.get('RequestedDeliveryDate') and qty(l.get('ScheduleLineOrderQuantity'))>0]

        confirmed = [(sap_date(l.get('ConfirmedDeliveryDate')), qty(l.get('OpenConfdDelivQtyInOrdQtyUnit')),

                      qty(l.get('DeliveredQtyInOrderQtyUnit')))

                     for l in lines if l.get('ConfirmedDeliveryDate')]

        # The two SAP schedule-line types represent the SAME order, not additive orders.

        confirmed_open = sum(max(0,q) for _,q,_ in confirmed)

        delivered = sum(max(0,deliv) for _,_,deliv in confirmed)

        ordered = sum(q for _,q in requested)

        for d,q,_ in confirmed:

            if d and q>0:

                records.append((d,q))

        # Remaining unconfirmed demand uses requested date; avoid double counting.

        unconfirmed = max(0,ordered-delivered-confirmed_open)

        if unconfirmed and requested:

            base = sum(q for _,q in requested)

            for d,q in requested:

                if d:

                    records.append((d,unconfirmed*q/base))

    result = window(records,as_of,'sales')

    result['quantity_basis'] = 'OPEN_CONFIRMED_PLUS_UNCONFIRMED_NOT_DOUBLE_COUNTED'

    return result



def training_rows():

    if not os.path.isfile(CSV_PATH):

        raise RuntimeError(f'Training CSV missing: {CSV_PATH}')

    with open(CSV_PATH,newline='',encoding='utf-8') as f:

        data=list(csv.DictReader(f))

    required = FEATURES + ['DemandNext7Days']

    if not data or any(k not in data[0] for k in required):

        raise RuntimeError(f'CSV needs columns {required}')

    x,y=[],[]

    for r in data:

        try:

            a=[qty(r[k]) for k in FEATURES]

            b=qty(r['DemandNext7Days'])

        except (ValueError,TypeError):

            continue

        if any(v < 0 for v in a) or b < 0:

            continue

        x.append(a); y.append(b)

    if len(x)<20:

        raise RuntimeError('Need at least 20 valid labelled training rows')

    return x,y



def token():

    url=os.getenv('AICORE_AUTH_URL','')

    if not url:

        raise RuntimeError('AICORE_AUTH_URL missing')

    r=requests.post(url,data={'grant_type':'client_credentials'},

        auth=(os.getenv('AICORE_CLIENT_ID',''),os.getenv('AICORE_CLIENT_SECRET','')),

        verify=VERIFY,timeout=60)

    r.raise_for_status()

    return r.json()['access_token']



def predict_tabpfn(features):

    x,y=training_rows()

    endpoint=os.getenv('TABPFN_INFERENCE_URL','')

    if not endpoint:

        api=os.getenv('AICORE_API_URL','').rstrip('/')

        dep=os.getenv('TABPFN_DEPLOYMENT_ID','')

        path=os.getenv('TABPFN_PREDICT_PATH','predict').lstrip('/')

        if not api or not dep:

            raise RuntimeError('Set TABPFN_INFERENCE_URL or AICORE_API_URL + TABPFN_DEPLOYMENT_ID')

        endpoint=f'{api}/inference/deployments/{dep}/{path}'

    payload={'task_config':{'task':'regression', 'tabpfn_config':{'n_estimators':8,'random_state':0},

                            'predict_params':{'output_type':'median'}},

             'x_train':x,'y_train':y,'x_test':[features]}

    r=requests.post(endpoint,json=payload,headers={'Authorization':f'Bearer {token()}',

                    'AI-Resource-Group':os.getenv('AICORE_RESOURCE_GROUP','default'),

                    'Content-Type':'application/json'},verify=VERIFY,timeout=180)

    if not r.ok:

        raise RuntimeError(f'TabPFN HTTP {r.status_code}: {r.text[:500]}')

    result=r.json()

    if isinstance(result,dict):

        result=next((result[k] for k in ('predictions','prediction','y_pred') if k in result),result)

        if isinstance(result,dict) and 'result' in result:

            result=result['result']

        if isinstance(result,dict):

            result=next((result[k] for k in ('predictions','prediction','y_pred','values','median','value') if k in result),result)

    while isinstance(result,list):

        if not result: raise RuntimeError('Empty TabPFN predictions')

        result=result[0]

    if isinstance(result,dict):

        result=next((result[k] for k in ('prediction','value','median') if k in result),result)

    predicted=qty(result)

    return max(0.0,predicted)



@app.get('/health')

def health():

    return {'status':'ok'}



@app.post('/predict-stock')

def predict_stock(request:StockRequest):

    try:

        as_of=request.as_of_date or date.today()

        material,plant=request.material.strip(),request.plant.strip()

        stock=current_stock(material,plant)

        safety=safety_stock_from_sap(material,plant)

        c=consumption(material,plant,as_of)

        po=purchase_orders(material,plant,as_of)

        sales=sales_demand(material,plant,as_of)

        features=[stock,c['quantity'],po['quantity'],sales['quantity']]

        predicted=predict_tabpfn(features)

        # Target: demand expected DURING the next 7 days (Days 1-7).
        # Purchase-order schedules are not verified incoming receipts.
        verified_incoming7 = 0.0
        target_stock = math.ceil(predicted + safety['quantity'])
        additional = max(0, math.ceil(target_stock - stock - verified_incoming7))
        projected_stock_without_replenishment = stock + verified_incoming7 - predicted
        return {
            'Material': material, 'Plant': plant, 'AsOfDate': str(as_of),
            'PredictionHorizonDays': 7,
            'CurrentStock': round(stock, 2), 'Consumption30D': c['quantity'],
            'OpenPO30D': po['quantity'], 'Demand30D': sales['quantity'],
            'Metrics': {'Consumption30D': c, 'OpenPO30D': po, 'Demand30D': sales},
            'PredictedDemandNext7Days': round(predicted, 2),
            'StockNeededAfter7Days': target_stock,
            'SafetyStock': safety['quantity'], 'SafetyStockDetails': safety,
            'VerifiedIncoming7D': verified_incoming7,
            'ProjectedStockAfter7DaysWithoutReplenishment': round(projected_stock_without_replenishment, 2),
            'AdditionalStockRequired': additional, 'Unit': 'PC',
            'TrainingDataSource': os.getenv('TRAINING_DATA_SOURCE', 'SYNTHETIC_TEST'),
            'Warning': ('Training labels are simulated 7-day demand proxies, not verified future SAP demand. '
                        'SAP historical fallbacks may be stale. PO schedule quantities are not verified receipts. '
                        'This output is a demonstration estimate, not a validated inventory forecast.')
        }

    except (requests.RequestException,ValueError,KeyError,RuntimeError) as exc:

        log.exception('Prediction failed')

        raise HTTPException(status_code=502,detail=str(exc)) from exc
