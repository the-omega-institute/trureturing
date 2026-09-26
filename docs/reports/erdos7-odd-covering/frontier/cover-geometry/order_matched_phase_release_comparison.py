#!/usr/bin/env python3
"""Exact complete-network margins for two separately realized phase releases.

The all20 square-pair scope and the all5 225q scope are alternatives. Each
retains all15 square-star freedoms and the declared625 network interfaces.
Input certificates and source constructions establish the gates; this program
checks original inventories and final rational comparisons, not their proofs.
"""
from argparse import ArgumentParser
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
import json

parser = ArgumentParser(description=__doc__)
parser.add_argument('--directory', type=Path, default=Path(__file__).parent)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
checks = Counter()
sources = {}


def check(name, condition):
    if not condition:
        raise ArithmeticError(name)
    checks[name] += 1


def read(name):
    raw = (args.directory / name).read_bytes()
    sources[name] = sha256(raw).hexdigest()
    return json.loads(raw)


head = read('all_square_star_phase_certificate.json')
network = read('order_matched_owner_network_certificate.json')
pairs = read('induced_square_pair_boundary_certificate.json')
Q = (7, 11, 13, 17, 19)
g, alpha = (F(head['constants'][s]) for s in ('g', 'alpha'))
gamma646 = F(head['worst']['gate'])
B = dict(zip(Q, map(F, head['coordinate_floor_factors'])))
fees = {q: g * F(8, 675) * F(1, q - 1) * prod(B[p] for p in Q if p != q) for q in Q}
linear = sorted(225*q for q in Q)
check('all5_originals_in_retained_inventory', set(linear) <= set(head['inventory']['remaining_linear_stars']))
check('all5_unique_originals', len(set(linear)) == 5)
check('all5_exact_source_floors', B == {q: F(5, 6) if q == 7 else F(q-2, q-1)-F(2, q*(q-2)) for q in Q})
check('worst_single_direct_fee', max(fees.values()) == fees[7] == F(85964226668567559143, 63163937458954886400000))
gamma225 = gamma646 - sum(fees.values(), F())
check('all5_gate', gamma225 == F(3650667248749677341466943, 306555643134127715328000000))
scope20 = next(s for s in pairs['scopes'] if s['scope'] == 'twenty')
gamma20 = F(scope20['worst']['gate'])
check('all20_gate', gamma20 == F(203129722400814193208791597, 20692505911553620784640000000))
check('all20_original_identity', scope20['released_square_pairs'] == sorted(q*q*s for q in Q for s in Q if q != s))
check('all20_retained_pairs', scope20['remaining_pairs'] == sorted(m*q*s for i, q in enumerate(Q) for s in Q[i+1:] for m in (1, 9)))
check('all15_square_stars_retained', pairs['previously_free_square_stars'] == head['inventory']['freed_square_stars'] and len(pairs['previously_free_square_stars']) == 15)
check('same_complete512', pairs['unchanged512_coefficients'] == head['complete512_coefficients'])
E115 = F(19740202146111572828188083, 495176015714152109959649689600)
results = {}
for r, owner_upper, tail, denominator20, denominator225 in (
    (3, F(8631, 1000000), E115, 36700, 12900),
    (4, F(397, 50000), F(8, 3)*E115, 23600, 10800),
):
    data = network['results'][str(r)]
    check('certified_owner_budget', F(data['total_owner_fee']) < owner_upper == F(data['simple_total_owner_fee_upper']))
    check('correct_large_owner_tail', F(data['complete_large_owner_tail']) == tail)
    check('same_large_owner_threshold', data['same_large_owner_threshold'] == 2**115)
    complete = owner_upper + F(1, 65536) + tail
    margin20, margin225 = (alpha*(gamma-complete) for gamma in (gamma20, gamma225))
    check('positive_all20_complete_network', margin20 > F(1, denominator20))
    check('positive_all5_complete_network', margin225 > F(1, denominator225))
    results[str(r)] = dict(owner_fee_strict_upper=str(owner_upper), large_owner_tail=str(tail),
        ordinary_fee=str(F(1, 65536)), total_fee_strict_upper=str(complete),
        all20=dict(projected_margin=str(margin20), density_denominator=denominator20,
                   remaining_linear_incidence_count=40, remaining_pair_incidence_count=20),
        all5_225=dict(projected_margin=str(margin225), density_denominator=denominator225,
                     remaining_linear_incidence_count=35, remaining_pair_incidence_count=40))
out = dict(schema='order-matched-phase-release-comparison-v1', status='PASS',
    source_sha256=sources, producer_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
    constants=dict(alpha=str(alpha), all20_head_gate=str(gamma20), all5_225_head_gate=str(gamma225)),
    direct225_fees={str(q): str(fees[q]) for q in Q}, released225_originals=linear,
    results=results, checks=dict(checks), check_count=sum(checks.values()),
    scopes_are_alternatives=True, new_lean_verification=False)
args.output.write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out, indent=2))
