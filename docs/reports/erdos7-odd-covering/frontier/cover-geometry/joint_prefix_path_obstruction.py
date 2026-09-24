#!/usr/bin/env python3
"""Actual even-cover obstruction to multiplying report 376's prefix caps.

The eight-point residual passes all odd-prime tree tests at its original
heights and admits one stronger marginal law. No law has pair caps 1/9.
This refutes tensorization from those conditions, not Erdős #7: the cover
is even, not divisor-closed, and not globally minimum. Alternate queries
use original numerical moduli but are not original forbidden events.
"""
from fractions import Fraction
from itertools import combinations, product
from math import prod
import json


def check(condition, message):
    if not condition:
        raise RuntimeError(message)


def crt(items):
    modulus = prod(m for _, m in items)
    value = 0
    for residue, factor in items:
        quotient = modulus // factor
        value += residue * quotient * pow(quotient, -1, factor)
    return value % modulus, modulus


H = 15
D = 2**H
S = {(i, j) for i in range(1, 5) for j in (i, i+1)}
weights = {edge: Fraction(1, 5) if edge in {(1, 1), (4, 5)} else Fraction(1, 10) for edge in S}
check(sum(weights.values()) == 1, 'law normalization')
row_mass = {i: sum(w for (a, b), w in weights.items() if a == i) for i in range(5)}
col_mass = {j: sum(w for (a, b), w in weights.items() if b == j) for j in range(7)}
check(max(row_mass.values()) <= Fraction(1, 3), 'strong row caps')
check(max(col_mass.values()) <= Fraction(1, 5), 'strong col caps')
rect_counts = [len(S.intersection(product(rows, cols))) for rows in combinations(range(5), 3) for cols in combinations(range(7), 5)]
check(len(rect_counts) == 210 and min(rect_counts) > 0, 'chain rectangle hitting')
check(all(any(i in rows for i, j in S) for rows in combinations(range(5), 3)), 'one-prime five tree')
check(all(any(j in cols for i, j in S) for cols in combinations(range(7), 3)), 'one-prime seven tree')

classes = []

def add(label, residue, modulus):
    check(modulus > 1 and 0 <= residue < modulus, 'AP range')
    classes.append((label, residue, modulus))

for j in range(1, H+1):
    add('dyadic-'+str(j), 2**(j-1)-1, 2**j)
add('pure5', 0, 5)
add('pure7', 0, 7)
outside = sorted(set(product(range(1, 5), range(1, 7))) - S)
check(len(outside) == 16, 'outside labels')
for e, (i, j) in enumerate(outside):
    residue, modulus = crt([(i, 5), (j, 7), (2**e-1, 2**e)])
    add('outside-'+str(e), residue, modulus)
add('pure3', 0, 3)
inside_with_q = [(i, j, k) for i, j in sorted(S) for k in (1, 2)]
for e, (i, j, k) in enumerate(inside_with_q):
    residue, modulus = crt([(i, 5), (j, 7), (k, 3), (2**e-1, 2**e)])
    add('inside-'+str(e), residue, modulus)
check(len(classes) == 50, 'class count')
check(len({m for _, _, m in classes}) == len(classes), 'distinct numerical moduli')
Q = 3*5*7*D
covered = bytearray(Q)
for label, residue, modulus in classes:
    count = (Q-1-residue)//modulus + 1
    covered[residue::modulus] = b'\1'*count
check(all(covered), 'whole cover')

last_i, last_j, last_k = inside_with_q[-1]
private = {}
for j in range(1, H+1):
    private['dyadic-'+str(j)] = crt([(last_i, 5), (last_j, 7), (last_k, 3), (2**(j-1)-1, D)])[0]
private['pure5'] = crt([(0, 5), (1, 7), (1, 3), (D-1, D)])[0]
private['pure7'] = crt([(1, 5), (0, 7), (1, 3), (D-1, D)])[0]
private['pure3'] = crt([(1, 5), (1, 7), (0, 3), (D-1, D)])[0]
for e, (i, j) in enumerate(outside):
    private['outside-'+str(e)] = crt([(i, 5), (j, 7), (1, 3), (D-1, D)])[0]
for e, (i, j, k) in enumerate(inside_with_q):
    private['inside-'+str(e)] = crt([(i, 5), (j, 7), (k, 3), (D-1, D)])[0]
for label, witness in private.items():
    hits = [name for name, residue, modulus in classes if witness % modulus == residue]
    check(hits == [label], 'private witness for '+label)
check(len(private) == 50, 'all private witnesses')

B = 5*7*D
covered_qfree = bytearray(B)
for label, residue, modulus in classes:
    if modulus % 3:
        count = (B-1-residue)//modulus + 1
        covered_qfree[residue::modulus] = b'\1'*count
residual = [x for x, covered_bit in enumerate(covered_qfree) if not covered_bit]
expected = sorted(crt([(i, 5), (j, 7), (D-1, D)])[0] for i, j in S)
check(residual == expected, 'actual R3 exact')

queries = []
for e, (i, j) in enumerate(sorted(S)):
    residue, modulus = crt([(i, 5), (j, 7), (2**e-1, 2**e)])
    hits = [x for x in residual if x % modulus == residue]
    check(len(hits) == 1 and hits[0] % 5 == i and hits[0] % 7 == j, 'query exact singleton')
    check(modulus in {m for _, _, m in classes}, 'query modulus from original palette')
    check((residue, modulus) not in {(r, m) for _, r, m in classes}, 'query not actual forbidden original')
    queries.append((residue, modulus))
check(len({m for r, m in queries}) == 8, 'distinct query moduli')
check(all(sum(x % m == r for r, m in queries) == 1 for x in residual), 'queries partition residual')

# All nontrivial odd-prime single / chain tests are q=3: 5, 7, (5,7), and q=5: 7.
B5 = 3*7*D
covered_5free = bytearray(B5)
for label, residue, modulus in classes:
    if modulus % 5:
        count = (B5-1-residue)//modulus + 1
        covered_5free[residue::modulus] = b'\1'*count
residual5 = [x for x, covered_bit in enumerate(covered_5free) if not covered_bit]
projection7 = {x % 7 for x in residual5}
check(len(residual5) == 12 and projection7 == set(range(1, 7)), 'actual R5 projection')
check(all(projection7.intersection(cols) for cols in combinations(range(7), 5)), 'q5 single-prime tree test')

# This independently exhibits non-extremality among unrestricted distinct covers.
small_even_cover = [(0, 2), (0, 3), (1, 4), (1, 6), (11, 12)]
check(all(any(x % m == r for r, m in small_even_cover) for x in range(12)), 'five-class comparison cover')

joint_cap = Fraction(1, 3)**2
joint_cost = len(S)*joint_cap
check(joint_cost == Fraction(8, 9) < 1, 'product-cap dual obstruction')

result = {
    'support': sorted(S),
    'chain_rectangle_count': len(rect_counts),
    'minimum_rectangle_intersection': min(rect_counts),
    'rectangle_intersection_histogram': {str(k): rect_counts.count(k) for k in sorted(set(rect_counts))},
    'strong_common_row_masses': {str(k): str(v) for k, v in row_mass.items()},
    'strong_common_col_masses': {str(k): str(v) for k, v in col_mass.items()},
    'joint_point_cap': str(joint_cap),
    'joint_dual_cost': str(joint_cost),
    'original_class_count': len(classes),
    'full_period': Q,
    'whole_cover': True,
    'distinct_numerical_moduli': True,
    'private_witness_count': len(private),
    'residual_period': B,
    'actual_R3_cardinality': len(residual),
    'actual_R3': residual,
    'actual_R5_cardinality': len(residual5),
    'actual_R5_mod7_projection': sorted(projection7),
    'distinct_query_count': len(queries),
    'query_moduli': [m for r, m in queries],
    'scope': 'even; irredundant; all relevant odd prime chain tests; not odd; not divisor closed; not globally minimum',
}
print(json.dumps(result, indent=2))
