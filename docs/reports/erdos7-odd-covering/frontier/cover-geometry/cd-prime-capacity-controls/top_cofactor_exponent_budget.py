"""Exact finite exponent-product certificate; no source phases are modeled.

The input inequalities remain mathematical hypotheses:
tau(m/d)<=5*d for composite d|m, and
tau(m/p**2)<=5*(p*p-p-1) for p**2|m.
This program audits their consequence under the declared exponent caps.
"""
import argparse
from itertools import combinations
import json
import math
from pathlib import Path

PRIMES = [p for p in range(5, 113)
          if all(p % k for k in range(2, math.isqrt(p) + 1))]
CAPS = {p: ({5: 15, 7: 13, 11: 12, 13: 11}.get(p, 2 if p < 29 else 1))
        for p in PRIMES}
assert len(PRIMES) == 27 and sum(CAPS.values()) == 77


def minimum_product(caps, total):
    # DP[k][s] minimizes product(e_i+1), using precisely the first k
    # primes and exact exponent sum s. None denotes an unreachable sum.
    table = [[None] * (total + 1)]
    table[0][0] = 1
    paths = {0: []}
    for p in PRIMES:
        row = [None] * (total + 1)
        new_paths = {}
        for s, product in enumerate(table[-1]):
            if product is None:
                continue
            for exponent in range(min(caps[p], total - s) + 1):
                target = s + exponent
                value = product * (exponent + 1)
                if row[target] is None or value < row[target]:
                    row[target] = value
                    new_paths[target] = paths[s] + [exponent]
        table.append(row)
        paths = new_paths
    witness = dict(zip(PRIMES, paths[total]))
    # Independent witness and local recurrence checks.
    assert sum(witness.values()) == total
    assert all(0 <= witness[p] <= caps[p] for p in PRIMES)
    assert math.prod(e + 1 for e in witness.values()) == table[-1][total]
    for i, p in enumerate(PRIMES):
        for s in range(total + 1):
            candidates = [table[i][s - e] * (e + 1)
                          for e in range(min(caps[p], s) + 1)
                          if table[i][s - e] is not None]
            assert table[i + 1][s] == (min(candidates) if candidates else None)
    return table[-1][total], witness, table


rows = []
for p in PRIMES:
    if CAPS[p] < 2:
        continue
    residual_caps = {
        q: 1 if q < p else CAPS[q] - 2 if q == p else CAPS[q]
        for q in PRIMES
    }
    minimum, witness, table = minimum_product(residual_caps, 24)
    bound = 5 * (p * p - p - 1)
    assert minimum > bound
    rows.append({
        'smallest_squared_prime': p,
        'residual_exponent_sum': 24,
        'residual_caps': residual_caps,
        'minimum_tau': minimum,
        'minimizer': {q: e for q, e in witness.items() if e},
        'guard_upper_bound': bound,
        'strict_gap': minimum - bound,
        'dp_table': table,
    })

# The squarefree >=26-prime case. Every 26-subset meets {5,7,11}
# in >=2 primes; selecting the two smallest members gives product<=77.
squarefree_cases = []
for absent in PRIMES + [None]:
    support = [p for p in PRIMES if p != absent]
    if len(support) < 26:
        continue
    small = [p for p in support if p in [5, 7, 11]]
    assert len(small) >= 2
    d = small[0] * small[1]
    assert d <= 77 and 2 ** 24 > 5 * d
    squarefree_cases.append({'omitted_prime': absent, 'chosen_composite': d})

# This exponent vector proves the relaxation still allows Omega=25.
# It is not an actual covering family or a realizable phase assignment.
exponents = {7: 13, 11: 12}
assert sum(exponents.values()) == 25
witness_checks = []
for a in range(14):
    for b in range(13):
        if a + b < 2:
            continue
        d = 7 ** a * 11 ** b
        residual_tau = (14 - a) * (13 - b)
        assert residual_tau <= 5 * d
        witness_checks.append({'divisor_exponents': [a, b], 'd': d,
                               'tau_m_over_d': residual_tau,
                               'upper_bound': 5 * d})
square_checks = []
for p, e in exponents.items():
    tau = math.prod((f - 1 if q == p else f + 1)
                    for q, f in exponents.items())
    bound = 5 * (p * p - p - 1)
    assert tau <= bound
    square_checks.append({'p': p, 'tau_m_over_p2': tau, 'bound': bound})
second_checks = []
for a in range(14):
    for b in range(12):
        if a + b < 2:
            continue
        d = 7 ** a * 13 ** b
        residual_tau = (14 - a) * (12 - b)
        assert residual_tau <= 5 * d
        second_checks.append({'divisor_exponents': [a, b], 'd': d,
                              'tau_m_over_d': residual_tau,
                              'upper_bound': 5 * d})
assert 12 * 12 <= 5 * (49 - 7 - 1)
assert 14 * 10 <= 5 * (169 - 13 - 1)
first_stock = {7 ** a * 11 ** b for a in range(12) for b in range(13)}
second_stock = {7 ** a * 13 ** b for a in range(12) for b in range(12)}
assert (len(first_stock), len(second_stock), len(first_stock & second_stock)) == (156, 144, 12)
assert len(first_stock | second_stock) == 288 > 205

# Joint numerical ceilings alone still admit a large shallow downset.
shallow_supports = [s for k in range(4) for s in combinations(PRIMES, k)]
shallow_stock = {math.prod(s): s for s in shallow_supports}
assert len(shallow_stock) == len(shallow_supports) == 3304
assert all(math.prod(t) in shallow_stock for s in shallow_supports
           for k in range(len(s) + 1) for t in combinations(s, k))
assert all(m % (p * p) != 0 for m in shallow_stock for p in PRIMES)
pair_fibers = triple_fibers = 0
mixed_ceilings = []
for d, s in shallow_stock.items():
    if len(s) < 2:
        continue
    count = sum(m % d == 0 for m in shallow_stock)
    assert count == (26 if len(s) == 2 else 1)
    assert count <= 5 * math.prod(p - 1 for p in s) <= 5 * d
    if len(s) == 2:
        pair_fibers += 1
        p, r = s
        mixed = 5 * (p - 1) * (r - 1) - 3 * (p + r - 2) + 5
        assert count <= mixed
        mixed_ceilings.append(mixed)
    else:
        triple_fibers += 1
assert (pair_fibers, triple_fibers, min(mixed_ceilings)) == (351, 2925, 95)

result = {
    'scope': 'Exact integer DP for exponent relaxation; whole-cover inequalities assumed.',
    'prime_caps': CAPS,
    'global_height_envelope': sum(CAPS.values()),
    'target_original_omega': 26,
    'squarefree_cases': squarefree_cases,
    'smallest_square_cases': rows,
    'consequence': 'Every actual top cofactor satisfying the assumed inequalities has Omega<=25.',
    'relaxation_omega25_witness': {
        'exponents': exponents,
        'all_composite_divisor_checks': witness_checks,
        'square_checks': square_checks,
        'interpretation': 'No claim of actual whole-cover or phase realizability.'
    },
    'shared_49_inventory_control': {
        'second_exponents': {7: 13, 13: 11},
        'second_composite_divisor_checks': second_checks,
        'second_square_checks': [
            {'p': 7, 'tau_m_over_p2': 144, 'bound': 205},
            {'p': 13, 'tau_m_over_p2': 140, 'bound': 775}],
        'individual_stock_sizes': [len(first_stock), len(second_stock)],
        'intersection_size': len(first_stock & second_stock),
        'union_size': len(first_stock | second_stock),
        'actual_shared_stock_upper_bound': 205,
        'interpretation': 'Separate exponent relaxations pass; simultaneous actual top labels are excluded.'
    },
    'rank_three_stock_control': {
        'stock_size': len(shallow_stock),
        'rank_counts': [math.comb(27, k) for k in range(4)],
        'omega_lcm': 27,
        'maximum_individual_rank': 3,
        'square_divisors': 0,
        'pair_fibers': pair_fibers,
        'pair_fiber_size': 26,
        'triple_fibers': triple_fibers,
        'triple_fiber_size': 1,
        'minimum_mixed_pair_ceiling': min(mixed_ceilings),
        'interpretation': 'Numerical stock ceilings only; no phases, actual guard residual, cover, selector or prefix payment.'
    },
}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
args.output.write_text(json.dumps(result, indent=2) + '\n')
for row in rows:
    print(row['smallest_squared_prime'], row['minimum_tau'],
          row['guard_upper_bound'], row['minimizer'])
print('squarefree_cases', len(squarefree_cases), 'max_d',
      max(row['chosen_composite'] for row in squarefree_cases))
print('omega25_witness_composite_checks', len(witness_checks))
print('second_witness_composite_checks', len(second_checks),
      'shared_stock', len(first_stock | second_stock), 'bound', 205)
print('rank_three_stock', len(shallow_stock), 'composite_fibers',
      pair_fibers + triple_fibers)
