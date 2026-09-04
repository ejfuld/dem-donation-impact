"""Marginal-impact model for 2026 Democratic donations. Prototype / exploration."""
import csv, math

SIG = {'H': 6.65, 'S': 6.69}   # implied margin SD in pct pts, backed out of Silver's own p & vote shares


def phi(z):
    return math.exp(-0.5 * z * z) / math.sqrt(2 * math.pi)


def phi_inv(p):
    p = min(max(p, 1e-12), 1 - 1e-12)
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
        return (((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    if p > 1 - pl:
        q = math.sqrt(-2 * math.log(1 - p))
        return -(((((c[0]*q+c[1])*q+c[2])*q+c[3])*q+c[4])*q+c[5]) / ((((d[0]*q+d[1])*q+d[2])*q+d[3])*q+1)
    q = p - 0.5
    r = q * q
    return (((((a[0]*r+a[1])*r+a[2])*r+a[3])*r+a[4])*r+a[5])*q / (((((b[0]*r+b[1])*r+b[2])*r+b[3])*r+b[4])*r+1)


def load(base='/home/claude/impact/data'):
    marg = {r['race']: (r['party'], float(r['margin']))
            for r in csv.DictReader(open(f'{base}/margins_2026-09-04.csv'))}
    rows = []
    for fn, ch in [('silver_house_2026-09-04.csv', 'H'), ('silver_senate_2026-09-04.csv', 'S')]:
        for r in csv.DictReader(open(f'{base}/{fn}')):
            tip = float(r['tipping'])
            if tip <= 0 or not r['dem_win'] or r['race'] not in marg:
                continue
            p = float(r['dem_win'])
            party, mu = marg[r['race']]
            z = phi_inv(p)
            rows.append(dict(ch=ch, race=r['race'], name=r['dem_last'], party=party,
                             rating=r['rating'], tip=tip, vpi=float(r['vpi']),
                             el=float(r['elasticity']), p=p, mu=mu, z=z,
                             invN=float(r['vpi']) / tip))
    for r in rows:
        r['sig'] = SIG[r['ch']] * r['el']          # elasticity scales race-specific volatility
        r['f0'] = phi(r['z']) / r['sig']            # density of margin at zero, per pct pt
        r['a_raw'] = r['invN'] * r['f0']            # oc P(one vote flips the seat)
        r['b_raw'] = r['vpi']                       # oc P(one vote flips the chamber)
        # implied P(pivotal | race tied), up to a common constant
        r['piv'] = r['tip'] / r['f0']
    return rows


if __name__ == '__main__':
    rows = load()
    comp = [r for r in rows if 0.02 < r['p'] < 0.98]
    comp.sort(key=lambda r: -r['tip'])
    print('race   ch  tip       f0       piv=tip/f0   b/a = vpi/a_raw')
    for r in comp[:14] + comp[-6:]:
        print('%-6s %s  %.6f  %.5f  %9.4f  %10.4f' %
              (r['race'], r['ch'], r['tip'], r['f0'], r['piv'], r['b_raw'] / r['a_raw']))
