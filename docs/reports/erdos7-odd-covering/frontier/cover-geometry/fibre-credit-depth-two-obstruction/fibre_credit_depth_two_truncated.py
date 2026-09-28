#!/usr/bin/env python3
"""Check exact duals for the stated depth-two fibre comparison.

All leaf weights and real thresholds fail this particular relaxed comparison
even with ternary query height2 and the pure-conditioned23/29 target.
Original nonternary tails are complete. No actual-family realization,
covering counterexample, or new Lean verification is asserted.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
import json
from math import prod
from pathlib import Path


def need(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


def calculate():
    qs = (5, 7, 11, 13, 17, 19)
    groups = ((0, 1), (2, 3, 4))
    choices = ((1, 3), (0, 1), (0, 0), (0, 1), (0, 1), (0, 0))
    budgets = [F(1, q-2) for q in qs]
    beta = [[budgets[i]*(int(l in groups[r])+int(l == s))
             for l in range(5)] for i, (r, s) in enumerate(choices)]
    supports = [tuple(d) for size in range(2, 7)
                for d in combinations(range(6), size)]
    need(len(supports) == 57, 'complete 57 mixed supports')

    def g(d):
        return [prod(1-beta[i][l] for i in range(6) if i not in d)
                for l in range(5)]

    gs = [g(d) for d in supports]
    bs = [prod(budgets[i] for i in d) for d in supports]
    initial = g(())
    affine = [initial[l]-sum((b*gd[l] for b, gd in zip(bs, gs)), F(0))
              for l in range(5)]
    names = ['w'+str(l) for l in range(5)]+['r', 'v']
    names += ['u_'+str(i) for i in range(57)]
    names += ['z_'+str(i) for i in range(57)]
    size = len(names)
    need(size == 121, 'LP variable count')
    rows, rhs, labels = [], [], []

    def row(coefficients, bound, label):
        rows.append({k: F(v) for k, v in coefficients.items() if v})
        rhs.append(F(bound))
        labels.append(label)

    for i, gd in enumerate(gs):
        for j, group in enumerate(groups):
            row({**{l: gd[l] for l in group}, 7+i: -1}, 0,
                'root epigraph D'+str(i)+' group'+str(j))
        for l in range(5):
            row({l: gd[l], 64+i: -1}, 0,
                'leaf epigraph D'+str(i)+' leaf'+str(l))
    for j, group in enumerate(groups):
        row({**{l: 1 for l in group}, 5: -1}, 0, 'r epigraph '+str(j))
    for l in range(5):
        row({l: 1, 6: -1}, 0, 'v epigraph '+str(l))
    unit_rows = []
    for k in range(size):
        unit_rows.append(len(rows))
        row({k: 1}, 1, 'unit cap '+names[k])
    need(len(rows) == 527, 'LP inequality count including exact repair caps')
    equality = {l: F(1) for l in range(5)}
    mass = affine+[F(0), F(0)]+[-b for b in bs]+[-b for b in bs]

    def primal(w):
        r = max(sum(w[l] for l in group) for group in groups)
        v = max(w)
        u = [max(sum(w[l]*gd[l] for l in group) for group in groups)
             for gd in gs]
        z = [max(w[l]*gd[l] for l in range(5)) for gd in gs]
        x = list(w)+[r, v]+u+z
        need(sum(w) == 1 and min(x) >= 0, 'nonnegative simplex primal')
        need(all(sum((a*x[k] for k, a in rr.items()), F(0)) <= bb
                 for rr, bb in zip(rows, rhs)), 'exact primal feasibility')
        return x

    uniform = primal([F(1, 5)]*5)
    fixed = primal([F(1, 4), F(1, 4), F(1, 4), F(0), F(1, 4)])
    need(dot(mass, uniform) == F(6074, 210375), 'published uniform F2')
    need(dot(mass, fixed) == F(118177, 1514700), 'published fixed F2')

    # Complete geometric nonternary tails; exact atoms below thirteen and mean.
    low = {1: F(1)}
    mean = F(1)
    for q in qs:
        cap = F(q-1, q-2)
        atoms = {1: 1-cap/q}
        atoms.update({n: cap*F(q-1, q**n) for n in range(2, 13)})
        updated = {}
        for a, pa in low.items():
            for n, pn in atoms.items():
                if a*n <= 12:
                    updated[a*n] = updated.get(a*n, F(0))+pa*pn
        low = updated
        mean *= 1+F(1, q-2)
    need(mean == F(2048, 935), 'complete nonternary first moment')

    def hinge(j, t):
        return j*mean-t+sum(((t-j*n)*p for n, p in low.items() if j*n < t), F(0))

    objectives = []
    target = F(615, 49)
    for t in range(1, 13):
        h = [hinge(j, t) for j in (1, 2, 3)]
        h0, hr, hv = h[0], h[1]-h[0], h[2]-h[1]
        need(min(h0, hr, hv) >= 0, 'nonnegative affine hinge coefficients')
        objective = [(target-t)*c for c in mass]
        objective[5] -= hr
        objective[6] -= hv
        fixed_score = dot(objective, fixed)-h0
        objectives.append(dict(t=t, h0=h0, hr=hr, hv=hv,
                               objective=objective, constant=-h0,
                               fixed_wstar_score=fixed_score))
    return dict(scope='Only the stated DT comparison vertex, whole-family H3<=2 query truncation, complete six nonternary tails, pure-conditioned outside23/29 gate. Exact LP reconstruction; solving is external and any bound requires a separate exact certificate. No actual-family realization or Lean claim.',
                target_plus_one=target, query_target=target-1,
                variables=names, nonnegative_variables=True,
                supports=supports, support_weights=bs, fibre_values=gs,
                initial=initial, mass_coefficients=mass,
                inequalities=rows, inequality_bounds=rhs, inequality_labels=labels,
                equality=equality, equality_bound=F(1), unit_cap_rows=unit_rows,
                nonternary_mean=mean, nonternary_small_atoms=low,
                objectives=objectives)


def check_duals(lp, records):
    need(isinstance(records, list), 'dual records list')
    output = []
    seen = set()
    for record in records:
        t = int(record['t'])
        need(1 <= t <= 12 and t not in seen, 'distinct allowed integer threshold')
        seen.add(t)
        obj = lp['objectives'][t-1]
        y = [F(0)]*len(lp['inequalities'])
        for index, value in record['inequality_duals'].items():
            i = int(index)
            need(0 <= i < len(y), 'inequality dual index')
            y[i] = F(value)
        lam = F(record['equality_dual'])
        need(min(y) >= 0, 'nonnegative inequality duals')
        columns = [lam*lp['equality'].get(k, F(0)) for k in range(len(lp['variables']))]
        for row, price in zip(lp['inequalities'], y):
            for k, value in row.items():
                columns[k] += value*price
        need(all(a >= c for a, c in zip(columns, obj['objective'])),
             'every exact dual column dominates its objective coefficient')
        upper = dot(lp['inequality_bounds'], y)+lam*lp['equality_bound']+obj['constant']
        output.append(dict(t=t, certified_score_upper=upper, nonpositive=upper <= 0))
    return dict(rows=output, all_thresholds_excluded=seen == set(range(1, 13))
                and all(r['nonpositive'] for r in output))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--duals', type=Path, default=Path(__file__).resolve().with_name(
        'fibre_credit_depth_two_truncated_duals.json'))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw = args.duals.read_bytes()
    lp = calculate()
    verified = check_duals(lp, json.loads(raw))
    need(verified['all_thresholds_excluded'], 'all twelve thresholds must have valid nonpositive duals')
    need(all(row['certified_score_upper'] < -F(7, 40) for row in verified['rows']),
         'every integer threshold has the stated strict margin')
    rows = []
    for row in sorted(verified['rows'], key=lambda item: item['t']):
        fixed = lp['objectives'][row['t'] - 1]['fixed_wstar_score']
        need(fixed <= row['certified_score_upper'], 'dual upper bounds the exact feasible candidate')
        rows.append(dict(t=row['t'], certified_score_upper=row['certified_score_upper'],
                         feasible_wstar_score=fixed,
                         exact_primal_dual_gap=row['certified_score_upper'] - fixed))
    summary = dict(scope=__doc__, dual_certificate_sha256=sha256(raw).hexdigest(),
                   variables=len(lp['variables']), inequalities=len(lp['inequalities']),
                   equalities=1, checked_dual_columns=12 * len(lp['variables']),
                   query_target=lp['query_target'],
                   nonternary_full_mean=lp['nonternary_mean'],
                   integer_thresholds=rows,
                   greatest_integer_upper=max(row['certified_score_upper'] for row in rows),
                   integer_upper_bound=-F(7, 40),
                   boundary='The strict integer margin is not asserted uniformly over all real thresholds. Integer-valued loads and the stated F2>0 normalization condition extend nonpositivity to every real threshold. These duals constrain this relaxed comparison only.')
    result = json.dumps(encode(summary), sort_keys=True, indent=2) + '\n'
    if args.output is None:
        expected = Path(__file__).resolve().with_suffix('.json')
        need(json.loads(expected.read_text()) == json.loads(result),
             'retained compact result agrees with the exact reconstruction')
        print(result, end='')
    else:
        args.output.write_text(result)


if __name__ == '__main__':
    main()
