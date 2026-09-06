"""Join Silver Bulletin forecast + media-market cost index + FEC money -> data.json"""
import csv, json, math, datetime, os
BASE = os.path.join(os.path.dirname(__file__), '..', 'data')
SIG = {'H': 6.65, 'S': 6.69}
ELECTION = datetime.date(2026, 11, 3)
CYCLE_START = datetime.date(2025, 1, 1)
MONEY_FLOOR = 1_000_000.0


def phi(z): return math.exp(-0.5 * z * z) / math.sqrt(2 * math.pi)


def phi_inv(p):
    p = min(max(p, 1e-9), 1 - 1e-9)
    a = [-3.969683028665376e+01, 2.209460984245205e+02, -2.759285104469687e+02,
         1.383577518672690e+02, -3.066479806614716e+01, 2.506628277459239e+00]
    b = [-5.447609879822406e+01, 1.615858368580409e+02, -1.556989798598866e+02,
         6.680131188771972e+01, -1.328068155288572e+01]
    c = [-7.784894002430293e-03, -3.223964580411365e-01, -2.400758277161838e+00,
         -2.549732539343734e+00, 4.374664141464968e+00, 2.938163982698783e+00]
    d = [7.784695709041462e-03, 3.224671290700398e-01, 2.445134137142996e+00, 3.754408661907416e+00]
    pl = 0.02425
    if p < pl:
        q = math.sqrt(-2 * math.log(p))
        return (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5])/((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    if p > 1 - pl:
        q = math.sqrt(-2 * math.log(1 - p))
        return -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5])/((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    q = p - .5; r = q * q
    return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q/(((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1)


def rd(f): return list(csv.DictReader(open(os.path.join(BASE, f))))


cost = {r['race']: float(r['costidx']) for r in rd('cost_index.csv')}
money = {r['race']: r for r in rd('money_2026-09-04.csv')}
marg = {r['race']: r for r in rd('margins_2026-09-04.csv')}

races = []
for fn, ch in [('silver_house_2026-09-04.csv', 'H'), ('silver_senate_2026-09-04.csv', 'S')]:
    for r in rd(fn):
        tip = float(r['tipping'])
        if tip <= 0 or not r['dem_win']:
            continue
        code = r['race']
        p = float(r['dem_win'])
        z = phi_inv(p)
        el = float(r['elasticity'])
        sig = SIG[ch] * el
        invN = float(r['vpi']) / tip
        m = money.get(code, {})
        receipts = float(m.get('receipts') or 0) or MONEY_FLOOR
        coh = max(float(m.get('coh') or 0), 0.0)
        cov = m.get('covend') or ''
        if cov:
            cd = datetime.date(*map(int, cov.split('-')))
            months_in = max((cd - CYCLE_START).days / 30.44, 1.0)
            months_left = max((ELECTION - cd).days / 30.44, 0.0)
        else:
            months_in, months_left = 20.0, 2.0
        rate = receipts / months_in
        races.append(dict(
            race=code, ch=ch, name=r['dem_last'], party=marg.get(code, {}).get('party', 'D'),
            rating=r['rating'] or ('Toss-up' if 0.4 < p < 0.6 else ''),
            tip=tip, vpi=float(r['vpi']), el=el, p=p,
            margin=float(marg.get(code, {}).get('margin') or 0),
            a=invN * phi(z) / sig,
            b=float(r['vpi']),
            cost=cost.get(code, 8.0),
            N=1.0 / invN,
            receipts=receipts, coh=coh,
            proj=coh + rate * months_left,
            rate=rate, cov=cov,
            match=m.get('match', 'none')))

# reach cost: price of reaching a fixed share (1%) of THIS electorate
import statistics as _st
_med = _st.median([r['N'] for r in races if r['ch'] == 'H'])
for r in races:
    r['Nrel'] = r['N'] / _med
    r['reach'] = r['cost'] * r['Nrel']

meta = dict(forecast_date='2026-09-04', built=datetime.date.today().isoformat(),
            n=len(races), sigma=SIG, money_floor=MONEY_FLOOR,
            defaults=dict(c_house=8.7, c_senate=8.7, sen_val=13.05, eta=0.5,
                          money='proj', theta=0.40))
json.dump(dict(meta=meta, races=races), open(os.path.join(BASE, '..', 'site', 'data.json'), 'w'),
          separators=(',', ':'))
print('wrote', len(races), 'races')
