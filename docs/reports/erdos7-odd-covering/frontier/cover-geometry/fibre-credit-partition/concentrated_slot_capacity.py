"""Exact source-concentrated first-depth slot relaxation for a fixed inventory.

No joint realization of different pair buckets or whole cover is asserted.
Run from the repository root, or pass an explicit --input path.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', default='docs/reports/erdos7-odd-covering/frontier/cover-geometry/fibre-credit-partition/fibre_credit_actual_roots_input.json')
    ap.add_argument('--output')
    args = ap.parse_args()
    raw = Path(args.input).read_bytes()
    data = json.loads(raw)
    checks = 0

    def need(ok, message):
        nonlocal checks
        checks += 1
        if not ok:
            raise ValueError(message)

    primes = data['primes']
    heights = dict(zip(primes, data['heights']))
    c = {q: F((q-1)*q**h, (q-2)*q**h+1) for q,h in heights.items()}
    roots = {(q,e):t for q,e,t in data['star_roots']}
    for q,h in heights.items():
        need(h >= 2, 'Concentrated profile has higher-depth holes')
        for e in range(1,h+1):
            need(roots[q,e] == (1 if q==5 else 2), 'Original complete same-root star assignment')
    selected = data['selected_witness']
    need(len({d for d,t in selected}) == len(selected), 'Distinct original cofactors')
    records = []
    vectors = []
    for t in (1,2):
        beta = {q: c[q]-1 if roots[q,1]==t else F(0) for q in primes}
        available = {}
        for q in primes:
            active = roots[q,1]==t
            tail = sum((F(1,q**e) for e in range(2,heights[q]+1)), F(0))
            # Pure depth-one root 0; higher pure holes and, when active,
            # higher star holes share root 1. First star removes root 2.
            v = [F(0), 1-q*(2 if active else 1)*tail]
            v += [F(0) if active else F(1)] + [F(1)]*(q-3)
            s = F(q)*(1-beta[q])/c[q]
            whole = int(s)
            frac = s-whole
            need(all(0<=z<=1 for z in v) and sum(v,F(0))==s, 'Same-source total root mass')
            extremal = [F(1)]*whole + ([frac] if frac else [])
            extremal += [F(0)]*(q-len(extremal))
            need(sorted(v,reverse=True)==extremal, 'Actual common-root layout gives a capped-simplex vertex')
            available[q] = [a for a,z in enumerate(v) if z==1]
            need(3 in available[q] and len(available[q])>=2, 'One shared old pq phase is a full cell')
            vectors.append({'root':t,'prime':q,'sum':str(s),'full_roots':available[q],'partial_mass':str(frac)})
        for p,q in combinations(primes,2):
            labels = [d for d,r in selected if r==t and d%p==d%q==0 and d%(p*p)!=0 and d%(q*q)!=0]
            rows,cols = available[p],available[q]
            full_slots = len(rows)*len(cols)+min(len(rows),len(cols))
            cap = full_slots-1
            need(len(labels)<=cap, 'Every first-depth bucket fits even with shared pq exclusion')
            cells = [(a,b) for a in rows for b in cols if (a,b)!=(3,3)]
            k = min(len(rows),len(cols))
            matching = next([(rows[i],cols[(i+shift)%k]) for i in range(k)]
                            for shift in range(k)
                            if all((rows[i],cols[(i+shift)%k])!=(3,3) for i in range(k)))
            slots = cells+matching
            need(len(slots)==cap, 'Full slot capacity after one globally shared cell exclusion')
            placement = slots[:len(labels)]
            occupancy = {e:placement.count(e) for e in set(placement)}
            doubles = [e for e,n in occupancy.items() if n==2]
            need(all(n<=2 for n in occupancy.values()), 'At most two per actual pair cell')
            need(len({a for a,b in doubles})==len(doubles) and len({b for a,b in doubles})==len(doubles), 'Doubles form a matching')
            need(all(a in rows and b in cols and (a,b)!=(3,3) for a,b in placement), 'All assigned slots have full mass and avoid the one old cell')
            records.append({'root':t,'pair':[p,q],'labels':len(labels),'full_slots':full_slots,'capacity_after_shared_pq':cap,'slack':cap-len(labels)})
    need(len(records)==110, 'All 55 pairs on both retained roots')
    minimum = min(r['slack'] for r in records)
    need(minimum==0, 'Tightest shallow bucket after shared-cell exclusion')
    result = {
        'contract':'FC36 original profile/star roots and numerical inventory; separate source-concentrated full-grid first-depth pair relaxations, one common old pq phase (3,3); no joint mixed-phase realization or all-height inference',
        'input':args.input,'input_sha256':sha256(raw).hexdigest(),
        'source_layout':'pure q at 0; pure q^e at 1+q^(e-1); first star at 2; higher star at 1+2q^(e-1)',
        'source_vectors':vectors,'buckets':records,'minimum_slack_after_shared_cell':minimum,
        'zero_deficit_buckets':len(records),'checks':checks,
    }
    serial = json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        Path(args.output).write_text(serial)
    else:
        print(serial,end='')
    print(json.dumps({'checks':checks,'buckets':len(records),'minimum_slack':minimum,'zero_deficit_buckets':len(records)},sort_keys=True))


if __name__=='__main__':
    main()
