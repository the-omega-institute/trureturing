#!/usr/bin/env python3
"""Fixed-schedule normalized comparison for rooted stars/triangles plus old57.

Inventory: every mixed modulus has support {3,q} or {3,p,q}, except arbitrary
5^b*7^c are also allowed. All actual numerical moduli are distinct, residues
are globally fixed and arbitrary, heights finite; arbitrary pure originals.
No parameter optimization and no Lean. Kernel and label-comparison proof
obligations use the separately audited normalized physical-law construction.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import argparse
import json

P = (3, 5, 7, 11, 13, 17, 19)
T = {5: 0, 7: 1, 11: 2, 13: 4, 17: 4, 19: 6}
C = {3: F(2), **{q: F(q-1, q-2-T[q]) for q in P[1:]}}
checks = {}

def require(name, condition):
    if name in checks:
        raise ValueError('duplicate check: ' + name)
    checks[name] = bool(condition)
    if not condition:
        raise ValueError(name)

def atom(p, k):
    return 1-C[p]/p if k == 0 else C[p]*F(p-1, p**(k+1))

def sum_low(ps, limit):
    table = {0: F(1)}
    for p in ps:
        table = {n: sum((table.get(j, F(0))*atom(p, n-j) for j in range(n+1)), F(0)) for n in range(limit+1)}
    return table

def low_by_convolution(ps, t, q):
    if q == 7:
        # M7=(1+K3)(1+K5)-1; t7=1 needs only M7=0.
        require('special_q7_threshold', t == 1)
        return {0: atom(3, 0)*atom(5, 0)}
    if t == 0:
        return {}
    d = sum_low(ps, max(0, t-2))
    return {0: atom(3, 0), **{
        m: sum((atom(3, k)*d.get(m//k-1, F(0)) for k in range(1, m+1) if m % k == 0), F(0))
        for m in range(1, t)
    }}

def low_by_enumeration(ps, t, q):
    """Independent direct low-event enumeration, integrating K3=0 exactly."""
    if t == 0:
        return {}, 0
    out = {m: F(0) for m in range(t)}
    retained = 0
    if q == 7:
        for k3 in range(t):
            for k5 in range(t):
                m = k3*(1+k5)+k5
                if m < t:
                    out[m] += atom(3, k3)*atom(5, k5)
                    retained += 1
        return out, retained
    out[0] = atom(3, 0)
    # For K3>=1 and M<t, sum(Kp)<=t-2; no omitted large Kp can contribute.
    for ks in product(range(max(1, t-1)), repeat=len(ps)):
        total = sum(ks)
        if total > t-2:
            continue
        mass = prod((atom(p, k) for p, k in zip(ps, ks)), start=F(1))
        for k3 in range(1, t):
            m = k3*(1+total)
            if m < t:
                out[m] += atom(3, k3)*mass
                retained += 1
    return out, retained

rows = []
enumerated_low_tuples = 0
for j, q in enumerate(P[1:]):
    ps = P[1:j+1]
    t = T[q]
    delta = F(t, q-2)
    require('cap_' + str(q), C[q] == F(q-1, q-2)/(1-delta))
    require('valid_law_' + str(q), 0 < C[q]/q < 1)
    mean = 1 + sum((C[p]/(p-1) for p in ps), F(0))
    if q == 7:
        mean += C[5]/4
    low = low_by_convolution(ps, t, q)
    independent, count = low_by_enumeration(ps, t, q)
    require('independent_low_' + str(q), low == independent)
    enumerated_low_tuples += count
    hinge = mean-t+sum(((t-m)*v for m, v in low.items()), F(0))
    charge = hinge/(q-2-t)
    require('positive_charge_' + str(q), charge > 0)
    rows.append({'prime': q, 'threshold': t, 'delta': delta, 'cap': C[q], 'old_primes': ps,
                 'rooted_count': 'K3*(1+sum(old Kp))' + ('+K5' if q == 7 else ''),
                 'full_mean': mean, 'low_atoms': low, 'hinge': hinge, 'charge': charge,
                 'independent_retained_low_tuples': count})

beta = sum((row['charge'] for row in rows), F(0))
s = 1-beta
require('beta_exact', beta == F(151394965582137942235816821971, 212386721462686388534153737500))
require('q7_exact', rows[1]['charge'] == F(41, 180))

# Complete query remains V=product(1+Kp). Explicit product1..5 formulas.
base = prod((atom(p, 0) for p in P))
ratios = {n: [atom(p, n-1)/atom(p, 0) for p in P] for n in (2, 3, 4, 5)}
lowV = {1: base, 2: base*sum(ratios[2], F(0)), 3: base*sum(ratios[3], F(0)),
        4: base*(sum(ratios[4], F(0))+sum((x*y for x, y in combinations(ratios[2], 2)), F(0))),
        5: base*sum(ratios[5], F(0))}
meanV = prod(1+C[p]/(p-1) for p in P)
B = meanV-6+sum(((6-n)*mass for n, mass in lowV.items()), F(0))
require('unchanged_B5', B == F(7247078934354555645408264629987543, 4613074987956458806693241537456250))
R = 5+B/s
target = F(565, 51)
limit = 1-B/(target-5)
Lambda = prod(C.values())
haar = s/Lambda
reserve = 1-(1+R)*F(51, 616)
post = haar*reserve
require('beta_below_exact_limit', beta < limit)
require('query_below_target', R < target)
require('beta_simple_bound', beta < F(713, 1000))
require('B_simple_bound', B < F(63, 40))
require('query_simple_bound', R < F(3010, 287) < F(21, 2))
require('Lambda_exact', Lambda == F(138240, 5929))
require('Haar_positive', haar > 0)
require('fresh_positive', post > 0)

# Extra originals are charged under this same preconditioning law, before
# the single final conditioning. Full numerical labels remain distinct.
# Each support pair's geometric inventory sum is gp*gq, gp=Cp/(p-1).
old1119 = C[11]/10*C[19]/18
old1719 = C[17]/16*C[19]/18
eta = old1119+old1719
require('old1119_full_inventory_cost', old1119 == F(1, 77))
require('old1719_full_inventory_cost', old1719 == F(1, 121))
require('two_extra_pair_inventory_cost', eta == F(18, 847))
require('extra_cost_fits_general_allowance', eta < F(1, 40))
require('general_allowance_fits_exact_budget', F(1, 40) < limit-beta)
require('base_coarse_loss', beta < F(143, 200))
require('coarse_extra_survival', F(1)-F(143, 200)-F(1, 40) == F(13, 50))
require('coarse_extra_query', F(5)+F(63, 40)/F(13, 50) == F(575, 52) < target)

def with_extra_cost(cost):
    full_s = s-cost
    full_R = 5+B/full_s
    full_haar = full_s/Lambda
    full_reserve = 1-(1+full_R)*F(51, 616)
    full_post = full_haar*full_reserve
    # A separate cancellation identity checks the conditioning denominator.
    cancelled = (F(155, 308)*full_s-F(51, 616)*B)/Lambda
    require('fresh_cancellation_' + str(cost), full_post == cancelled)
    require('extra_query_' + str(cost), full_R < F(575, 52) < target)
    require('extra_positive_' + str(cost), full_s > 0 and full_post > 0)
    return {'extra_cost_upper': cost, 'total_charge_upper': beta+cost,
            'survivor_probability_lower': full_s, 'query_upper': full_R,
            'query_gap': target-full_R, 'Haar_survivor_lower': full_haar,
            'fresh_23_29_relative_reserve': full_reserve, 'fresh_23_29_Haar_lower': full_post,
            'remaining_same_law_charge_budget': limit-beta-cost}

extra_cases = {'arbitrary_weighted_extras_at_most_one_fortieth': with_extra_cost(F(1, 40)),
               'whole_old1119_and_old1719': with_extra_cost(eta)}

constants = {
    'beta': beta, 'survivor_probability_lower': s, 'full_query_mean': meanV, 'B5': B,
    'query_upper': R, 'target': target, 'query_gap': target-R, 'exact_beta_limit': limit,
    'extra_same_law_charge_budget': limit-beta, 'source_Haar_density_cap': Lambda,
    'Haar_survivor_lower': haar, 'fresh_23_29_relative_reserve': reserve,
    'fresh_23_29_Haar_lower': post,
}
result = {'scope': __doc__, 'parameters': {'primes': P, 'thresholds': T, 'caps': C}, 'rows': rows,
          'constants': constants, 'decimal': {k: float(v) for k, v in constants.items()},
          'extra_inventory_costs': {'whole_old1119': old1119, 'whole_old1719': old1719},
          'extra_cases': extra_cases,
          'extra_case_decimals': {name: {k: float(v) for k, v in case.items()} for name, case in extra_cases.items()},
          'independent_retained_low_tuples': enumerated_low_tuples,
          'checks': checks, 'passed_count': len(checks)}

def encode(x):
    if isinstance(x, F):
        return str(x)
    raise TypeError(type(x).__name__)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
out = parser.parse_args().output
out.write_text(json.dumps(result, indent=2, default=encode)+'\n')
print(json.dumps({'constants': constants, 'extra_cases': extra_cases, 'independent_retained_low_tuples': enumerated_low_tuples,
                  'passed_count': len(checks), 'output': str(out)}, indent=2, default=encode))
