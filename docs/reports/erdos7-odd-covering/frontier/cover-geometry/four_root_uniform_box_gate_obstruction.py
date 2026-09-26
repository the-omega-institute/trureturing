#!/usr/bin/env python3
"""Exact upper obstruction for a proposed constant four-root response box.

This tests a sufficient comparison response, not an actual covering family.
All finite heights remain in the pinned full512 fee table. Only Python's
standard library is required; run with -I -S -B -O.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import json
from math import prod
from pathlib import Path

p = ArgumentParser(description=__doc__)
p.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
p.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
a = p.parse_args()
checks = Counter()

def ck(name, value):
    if not value:
        raise ArithmeticError(name)
    checks[name] += 1

name = 'remaining33_global_root_exclusion_certificate.json'
pin = 'dd00b0e9f6a93713d437394c368a4ef81407cabd5ecb931ae7753926d9d8c3e4'
raw = (a.directory / name).read_bytes()
ck('complete_fee_source_pin', sha256(raw).hexdigest() == pin)
base = json.loads(raw)
Q = (7, 11, 13, 17, 19)
r = tuple(F(1, q - 1) for q in Q)
sq = tuple(F(1, q * (q - 2)) for q in Q)
Z = tuple(1 - 4 * r[k] - (3 if k == 0 else 2) * sq[k] for k in range(5))
edges = tuple(combinations(range(5), 2))
beta = tuple(sq[i] * r[j] + r[i] * sq[j] + 2 * r[i] * r[j] for i, j in edges)
strict_sum = sum((b / (Z[i] * Z[j]) for (i, j), b in zip(edges, beta)), F())
ck('all_unary_masses_positive', min(Z) > 0)
ck('strict_normalized_edge_sum', strict_sum == F(12120375130167, 14190523605440) < 1)

def matching_sum(vertices):
    # Independently enumerate every matching on an induced K5. Matchings
    # have at most two edges, but this construction does not encode that.
    es = tuple(k for k, e in enumerate(edges) if set(e) <= vertices)
    total = F()
    for size in range(len(es) + 1):
        for chosen in combinations(es, size):
            occupied = [v for k in chosen for v in edges[k]]
            if len(set(occupied)) != len(occupied):
                continue
            total += (-1) ** size * prod(beta[k] for k in chosen) * prod(
                Z[v] for v in vertices - set(occupied))
    return total

H = []
for T in range(32):
    vertices = {k for k in range(5) if not (T >> k) & 1}
    h = matching_sum(vertices)
    ck('induced_matching_response_positive', 0 < h <= prod(Z[k] for k in vertices))
    H.append(h)
ck('empty_response', H[0] == F(1413576886723, 132229083987000))
ck('full_query_response', H[31] == 1)
g = F(base['constants']['g'])
C = list(map(F, base['combined512_coefficients']))
ck('coefficient_inventory', len(C) == 512 and min(C) >= 0)
ck('source_coefficient', g == F(200163067, 201247200))
for k in range(1, 5):
    C[32 * 9 + (1 << k)] += g * sq[k]
ck('guarded_additions_outside_mode_zero', all((32 * 9 + (1 << k)) >= 32 for k in range(1, 5)))
mode0_fee = sum((C[T] * H[T] for T in range(32)), F())
coefficient = g * H[0] - mode0_fee
ck('positive_coefficient', coefficient > 0)

I = (0, 1, 2, 4, 5)
J = tuple(m for m in range(20) if m != 5)
corner = (4, 6)
w = {l: F(1 if l == corner[0] else 2, 9) for l in I}
v = {m: F(3 if m == corner[1] else 4, 75) for m in J}
ck('probability_corner', sum(w.values()) == sum(v.values()) == 1)
live_mass = sum((w[l] * v[m] for l, m in product(I, J) if not (l < 3 and m < 5)), F())
ck('corner_live_mass', live_mass == F(37, 45))
upper = coefficient * live_mass
target = F(193, 100000)
ck('every_field_obstruction', upper < target)
ck('exact_upper', upper == F(313861928665847176011205397, 165540047292428966277120000000))
out = dict(
    schema='four-root-constant-response-box-gate-obstruction-v1', status='PASS',
    new_lean_verification=False,
    scope='All nonnegative fields bounded by one on the specified constant response box, at corner (4,6); no actual phase signature or covering counterexample is asserted.',
    source_sha256={name: pin}, script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
    Q=Q, unary_masses=list(map(str, Z)), edges=[list(e) for e in combinations(Q, 2)],
    pair_caps=list(map(str, beta)), normalized_edge_sum=str(strict_sum),
    all32_response_values=list(map(str, H)), source_coefficient=str(g),
    complete512_coefficients=list(map(str, C)), mode_zero_fee=str(mode0_fee),
    mode_zero_net_coefficient=str(coefficient), corner=corner, corner_live_mass=str(live_mass),
    universal_field_upper=str(upper), universal_field_upper_decimal=float(upper),
    target=str(target), exact_shortfall=str(target - upper),
    proof='All central mode-zero selectors equal w_l v_m; their cost and mass share the same factor sum w_l v_m theta(l,m). Drop all other nonnegative fees, then use 0<=theta<=1 and the positive net coefficient.',
    checks=dict(checks), check_count=sum(checks.values()))
a.output.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: out[k] for k in ('status', 'check_count', 'universal_field_upper', 'target', 'exact_shortfall')}))
