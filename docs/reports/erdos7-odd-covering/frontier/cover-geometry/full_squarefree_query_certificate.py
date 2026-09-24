#!/usr/bin/env python3
"""Finite127-label squarefree query extension of the actual20-label family.

Checks all phase zero/nonzero patterns and weighted zero/one/other CRT
patterns. No enumeration of the full period; no all-height identification
of finite residues and no Lean. Every query uses the same law H(.|U).
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
from pathlib import Path
import argparse
import hashlib
import json

P = (3, 5, 7, 11, 13, 17, 19)
Q0 = P[1:]
M = prod(P)
ORIGINALS = tuple(combinations(Q0, 3))
D0 = tuple(S for size in range(1, 8) for S in combinations(P, size))
checks = {}

def require(name, condition):
    if name in checks:
        raise ValueError('duplicate check: '+name)
    checks[name] = bool(condition)
    if not condition:
        raise ValueError(name)

def is_bad(zero):
    return 3 in zero and len(zero-{3}) >= 3

def phase_fibre(T, zero_fixed):
    """Count one actual phase's survivor fibre; all nonzero phases are equal."""
    free = tuple(p for p in P if p not in T)
    survivor = total = 0
    for bits in product((0, 1), repeat=len(free)):
        zeros = set(zero_fixed) | {p for p, bit in zip(free, bits) if bit == 0}
        weight = prod(p-1 if bit else 1 for p, bit in zip(free, bits))
        total += weight
        if not is_bad(zeros):
            survivor += weight
    return survivor, total

phase_rows = []
phase_patterns = 0
phase_free_patterns = 0
for T in D0:
    d = prod(T)
    all_one, total = phase_fibre(T, set())
    require('fibre_cardinality_'+str(d), total == M//d)
    values = []
    for bits in product((0, 1), repeat=len(T)):
        phase_patterns += 1
        phase_free_patterns += 2**(7-len(T))
        zeros = {p for p, bit in zip(T, bits) if bit == 0}
        val, _ = phase_fibre(T, zeros)
        values.append(val)
    require('all_one_phase_maximizes_'+str(d), all_one == max(values))
    phase_rows.append({'modulus': d, 'support': T, 'all_one_survivor_fibre_count': all_one,
                       'minimum_phase_survivor_fibre_count': min(values),
                       'maximizing_zero_nonzero_pattern_count': sum(v == all_one for v in values)})

b = [0]*20
gram = [[0]*20 for _ in range(20)]
counts = {name: 0 for name in ('period', 'deleted', 'survivors', 'raw_hinge', 'deleted_hinge', 'full_squarefree_load', 'surviving_full_squarefree_load')}
histogram = {}
positive_deleted_points = []
for tags in product((0, 1, 2), repeat=7):
    zeros = {p for p, tag in zip(P, tags) if tag == 0}
    ones = {p for p, tag in zip(P, tags) if tag == 1}
    weight = prod(p-2 if tag == 2 else 1 for p, tag in zip(P, tags))
    load = 2**len(ones)-1
    direct = sum(set(T) <= ones for T in D0)
    if load != direct:
        raise ValueError('squarefree load identity')
    hinge = max(load-5, 0)
    hits = [i for i, S in enumerate(ORIGINALS) if 3 in zeros and set(S) <= zeros]
    bad = bool(hits)
    counts['period'] += weight
    counts['deleted'] += weight*bad
    counts['survivors'] += weight*(not bad)
    counts['raw_hinge'] += weight*hinge
    counts['deleted_hinge'] += weight*hinge*bad
    counts['full_squarefree_load'] += weight*load
    counts['surviving_full_squarefree_load'] += weight*load*(not bad)
    histogram[load] = histogram.get(load, 0)+weight
    if bad and hinge:
        positive_deleted_points.append({'zeros': sorted(zeros), 'ones': sorted(ones), 'weight': weight, 'hinge': hinge, 'hit_indices': hits})
    for i in hits:
        b[i] += weight*hinge
        for j in hits:
            gram[i][j] += weight*hinge

require('query_inventory_127', len(D0) == 127)
require('phase_pattern_count', phase_patterns == 3**7-1 == 2186)
require('phase_free_pattern_count', phase_free_patterns == 127*128 == 16256)
require('total_period', counts['period'] == M == 4849845)
require('unchanged_deleted_set', counts['deleted'] == 25127)
require('unchanged_survivor_set', counts['survivors'] == 4824718)
require('exact_positive_deleted_pattern_count', len(positive_deleted_points) == 20)
require('positive_deleted_geometry', all(len(x['zeros']) == 4 and 3 in x['zeros'] and len(x['ones']) == 3 and x['weight'] == 1 and x['hinge'] == 2 and len(x['hit_indices']) == 1 for x in positive_deleted_points))
for i in range(20):
    require('weighted_b_'+str(i), b[i] == 2)
    for j in range(20):
        require('weighted_Q_'+str(i)+'_'+str(j), gram[i][j] == (2 if i == j else 0))

# Independently derive the raw histogram as coefficients of product(p-1+t).
poly = [1]
for p in P:
    nxt = [0]*(len(poly)+1)
    for r, value in enumerate(poly):
        nxt[r] += (p-1)*value
        nxt[r+1] += value
    poly = nxt
require('histogram_polynomial', histogram == {2**r-1: v for r, v in enumerate(poly)})
require('raw_hinge_polynomial', counts['raw_hinge'] == sum(max(2**r-6, 0)*v for r, v in enumerate(poly)) == 746946)
require('unconditional_load_product', counts['full_squarefree_load'] == prod(p+1 for p in P)-M)
require('conditional_load_fibre_sum', counts['surviving_full_squarefree_load'] == sum(row['all_one_survivor_fibre_count'] for row in phase_rows) == 6754324)

delta = sum((F(b[i], M)**2 / F(gram[i][i], M) for i in range(20)), F(0))
require('projection_exact', delta == F(40, M) == F(8, 969969))
require('projection_saturates_actual_debit', delta == F(counts['deleted_hinge'], M) > 0)
raw_hinge = F(counts['raw_hinge'], M)
query = F(counts['surviving_full_squarefree_load'], counts['survivors'])
require('raw_hinge_exact', raw_hinge == F(14646, 95095))
require('finite_query_exact', query == F(3377162, 2412359))
require('finite_hinge_certificate', query <= 5+(raw_hinge-delta)/F(counts['survivors'], M))

result = {'scope': __doc__, 'primes': P, 'period': M, 'query_count': len(D0),
          'phase_pattern_count': phase_patterns, 'phase_free_pattern_count': phase_free_patterns,
          'phase_rows': phase_rows, 'weighted_counts': counts, 'load_histogram': histogram,
          'positive_deleted_points': positive_deleted_points, 'weighted_b_counts': b, 'weighted_Q_counts': gram,
          'raw_hinge': raw_hinge, 'exact_projection_and_deleted_hinge': delta,
          'finite_squarefree_query_sum': query,
          'scope_boundary': 'Finite nonunit squarefree D0 only. A larger finite query family for the same law can retain these maximizing phases and this debit. P-adic all-height use requires explicitly lifting nu with independent Haar higher digits; no full R_P value or target bound is claimed by this check.',
          'checks': checks, 'passed_count': len(checks)}

def encode(x):
    if isinstance(x, F):
        return str(x)
    raise TypeError(type(x).__name__)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
out = args.output
out.write_text(json.dumps(result, indent=2, default=encode)+'\n')
print(json.dumps({k: result[k] for k in ('period', 'query_count', 'phase_pattern_count', 'phase_free_pattern_count', 'weighted_counts', 'raw_hinge', 'exact_projection_and_deleted_hinge', 'finite_squarefree_query_sum', 'passed_count')}, indent=2, default=encode))
print(hashlib.sha256(out.read_bytes()).hexdigest())
