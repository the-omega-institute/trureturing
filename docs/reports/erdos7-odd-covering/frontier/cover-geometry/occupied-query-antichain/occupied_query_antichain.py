#!/usr/bin/env python3
"""Actual twenty-label antichain for occupied-query deletion criteria.

Enumerates 3^7 patterns (zero, one, other), weighted by their exact Haar
cardinality; never enumerates the full period. No Lean and no claim about
the complete nonunit divisor-query load.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, prod
from pathlib import Path
import argparse
import hashlib
import json

Q = (5, 7, 11, 13, 17, 19)
P = (3,) + Q
M = prod(P)
SUPPORTS = tuple(combinations(Q, 3))
LABELS = {S: 3*prod(S) for S in SUPPORTS}
checks = {}

def require(name, condition):
    if name in checks:
        raise ValueError('duplicate check: ' + name)
    checks[name] = bool(condition)
    if not condition:
        raise ValueError(name)

require('twenty_distinct_labels', len(set(LABELS.values())) == 20)
require('period', M == 4849845)
require('all_labels_shallow', max(LABELS.values()) < 10**9)
require('numerical_antichain', all(a == b or a % b != 0 for a in LABELS.values() for b in LABELS.values()))
for S, d in LABELS.items():
    require('squarefree_rooted_' + str(d), d % 9 != 0 and all(d % (q*q) != 0 for q in Q) and d % 3 == 0)
    # CRT guarantees one point from these actual coordinate assignments.
    zero_set = {3, *S}
    hit = [T for T in SUPPORTS if set(T) <= zero_set]
    require('private_point_' + str(d), hit == [S])

counts = {name: 0 for name in ('total', 'deleted', 'survivors', 'raw_hinge', 'deleted_hinge', 'query_load', 'surviving_query_load')}
query_counts = {S: 0 for S in SUPPORTS}
histogram = {}
survivor_histogram = {}
patterns = 0
for state in product(range(3), repeat=len(P)):
    patterns += 1
    weight = prod(p-2 if tag == 2 else 1 for p, tag in zip(P, state))
    zero = {p for p, tag in zip(P, state) if tag == 0}
    one = {p for p, tag in zip(P, state) if tag == 1}
    actual_hits = [S for S in SUPPORTS if 3 in zero and set(S) <= zero]
    bad = bool(actual_hits)
    if bad != (3 in zero and len(zero-{3}) >= 3):
        raise ValueError('deleted set structural characterization')
    query_hits = [S for S in SUPPORTS if 3 in one and set(S) <= one]
    load = len(query_hits)
    if load != (comb(len(one-{3}), 3) if 3 in one and len(one-{3}) >= 3 else 0):
        raise ValueError('load structural characterization')
    hinge = max(load-5, 0)
    counts['total'] += weight
    counts['deleted'] += weight*bad
    counts['survivors'] += weight*(not bad)
    counts['raw_hinge'] += weight*hinge
    counts['deleted_hinge'] += weight*hinge*bad
    counts['query_load'] += weight*load
    counts['surviving_query_load'] += weight*load*(not bad)
    histogram[load] = histogram.get(load, 0)+weight
    survivor_histogram[load] = survivor_histogram.get(load, 0)+weight*(not bad)
    for S in query_hits:
        query_counts[S] += weight*(not bad)

require('pattern_count', patterns == 3**7 == 2187)
require('weighted_total_period', counts['total'] == M)
require('deleted_structural_characterization', True)
require('load_structural_characterization', True)
require('deleted_count', counts['deleted'] == 25127)
require('survivor_count', counts['survivors'] == 4824718)
require('raw_hinge_count', counts['raw_hinge'] == 345)
require('deleted_hinge_count', counts['deleted_hinge'] == 0)
require('query_load_count', counts['query_load'] == counts['surviving_query_load'] == 30960)

# Separate64-pattern zero/one calculations reproduce key counts.
zero_count = sum((prod(q-1 for q in Q if q not in S) for n in range(3, 7) for S in combinations(Q, n)), 0)
hinge_count = sum((max(comb(n, 3)-5, 0)*prod(q-1 for q in Q if q not in S) for n in range(3, 7) for S in combinations(Q, n)), 0)
require('independent_deleted_count', zero_count == counts['deleted'])
require('independent_hinge_count', hinge_count == counts['raw_hinge'])
require('hinge_closed_form', 5*sum(q-1 for q in Q)+15 == counts['raw_hinge'])
require('query_mass_sum_closed_form', sum(M//d for d in LABELS.values()) == counts['query_load'])
for S, d in LABELS.items():
    # This query is entirely in U and attains the upper bound H(C)/H(U).
    require('maximizing_query_' + str(d), query_counts[S] == M//d)

H_W = F(counts['deleted'], M)
H_U = F(counts['survivors'], M)
hinge = F(counts['raw_hinge'], M)
occupied = F(counts['surviving_query_load'], counts['survivors'])
exp_certificate = 8**16-M*3**16
require('H_W_exact', H_W == F(25127, 4849845))
require('H_U_exact', H_U == F(4824718, 4849845))
require('hinge_exact', hinge == F(23, 323323) > 0)
require('occupied_query_sum_exact', occupied == F(15480, 2412359))
require('exponential_integer_certificate', exp_certificate == 72705052102411 > 0)
require('exp_taylor_lower_base', sum((F(1), F(1), F(1, 2), F(1, 6))) == F(8, 3))
require('exponential_threshold', F(4) > F(51863873, 25500000))
require('all_one_point_has_max_load', histogram[20] == 1 and survivor_histogram[20] == 1)

result = {
    'scope': __doc__, 'primes': P, 'period': M, 'pattern_count': patterns,
    'original_residue': 0, 'query_residue': 1,
    'labels': [{'outside_support': S, 'modulus': d, 'query_mass_under_H_conditioned_U': F(query_counts[S], counts['survivors'])} for S, d in LABELS.items()],
    'weighted_counts': counts, 'load_histogram': histogram, 'surviving_load_histogram': survivor_histogram,
    'H_W': H_W, 'H_U': H_U, 'raw_hinge': hinge, 'deleted_hinge': F(0), 'occupied_query_sum': occupied,
    'exponential_integer_certificate': exp_certificate,
    'refuted_claims': [
        'A universal c>0 giving E_H[1_W(L_F-5)+] >= c E_H[(L_F-5)+] for all actual irredundant rooted arithmetic families with simultaneous occupied-label maximizing query phases.',
        'A universal upper bound log E_H[1_U exp(L_F)] <= 51863873/25500000 for these families; this example gives log moment >4 by a rational exponential certificate.',
    ],
    'not_refuted': 'No assertion about the complete nonunit divisor-query load, existence of a desired common survivor law, R<565/51, or unrestricted Erdos7 is refuted.',
    'checks': checks, 'passed_count': len(checks),
}

def encode(x):
    if isinstance(x, F):
        return str(x)
    raise TypeError(type(x).__name__)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
out = args.output
out.write_text(json.dumps(result, indent=2, default=encode)+'\n')
print(json.dumps({key: result[key] for key in ('period', 'pattern_count', 'weighted_counts', 'H_W', 'H_U', 'raw_hinge', 'deleted_hinge', 'occupied_query_sum', 'exponential_integer_certificate', 'passed_count')}, indent=2, default=encode))
print(hashlib.sha256(out.read_bytes()).hexdigest())
