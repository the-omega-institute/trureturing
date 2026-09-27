#!/usr/bin/env python3
"""Exact phase-excess and same-law comparison controls for Report450 section9."""
import argparse
from fractions import Fraction as F
from itertools import combinations
from math import prod
from pathlib import Path
import json
import random


def require(value, label):
    if not value:
        raise ValueError(label)


primes = (3, 5, 7)
pure_floor = prod(F(p-2, p-1) for p in primes)
mixed_ceiling = sum(prod(F(1, p-2) for p in support)
                    for size in (2, 3) for support in combinations(primes, size))
source_reserve = 1-mixed_ceiling
haar_reserve = pure_floor*source_reserve
require((pure_floor, mixed_ceiling, source_reserve, haar_reserve)
        == (F(5, 16), F(2, 3), F(1, 3), F(5, 48)), 'three-prime reserve constants')
# Actual distinct-modulus cores, retaining all labels at heights (2,1,1).
period = 315
moduli = [d for d in range(2, period+1) if period % d == 0]
pure_moduli = {3, 9, 5, 7}
generator = random.Random(850)
core_results = []
for trial in range(130):
    residues = {d: trial if trial < 2 else generator.randrange(d) for d in moduli}
    pure_survivors = {x for x in range(period)
                      if all(x % d != residues[d] for d in pure_moduli)}
    survivors = {x for x in pure_survivors
                 if all(x % d != residues[d] for d in moduli)}
    haar = F(len(survivors), period)
    source = F(len(survivors), len(pure_survivors))
    require(haar >= haar_reserve and source >= source_reserve, 'actual core reserve')
    core_results.append((haar, source))

# The actual deep-collision construction: 286 original labels on a
# 143-point outside carrier.  No enumeration of the enormous retained
# period is performed; the original CRT predicates are kept explicitly.
p, q, M = 11, 13, 1
points = [(u, v) for u in range(p) for v in range(q)]
retained = [3**(M+t)*5**(M+p*q-1-t) for t in range(p*q)]
labels = [(p*d, p, u, d, 0) for (u, v), d in zip(points, retained)]
labels += [(q*d, q, v, d, 1) for (u, v), d in zip(points, retained)]
require(len({m for m, *_ in labels}) == 286, 'original numerical distinctness')
for first, second in combinations(labels, 2):
    require(first[0] % second[0] and second[0] % first[0], 'original incomparability')
require(all(2 % d != residue for _, _, _, d, residue in labels), 'literal integer2 hole')

phase_events = {(d, residue): set() for d in retained for residue in (0, 1)}
phase_costs = []
for index, (u, v) in enumerate(points):
    active = {}
    for _, outside, outside_residue, d, residue in labels:
        coordinate = u if outside == p else v
        if coordinate == outside_residue:
            active.setdefault(d, set()).add(residue)
            phase_events[d, residue].add(index)
    repeated = [d for d, phases in active.items() if len(phases) > 1]
    require(repeated == [retained[index]], 'unique repeated projected modulus')
    excess = sum(F(len(phases)-1, d) for d, phases in active.items())
    source_excess = F(8, 3)*excess
    require(excess == F(1, retained[index]) < haar_reserve, 'deep Haar excess')
    require(source_excess < source_reserve, 'deep source excess')
    phase_costs.append(excess)

# Exact same-law identity under a single explicitly nonuniform eta.
weights = [1 + (i % 7) for i in range(len(points))]
normalizer = sum(weights)
def mass(event):
    return F(sum(weights[i] for i in event), normalizer)
integrated = sum(F(weights[i], normalizer)*phase_costs[i] for i in range(len(points)))
merged = F(0)
for d in retained:
    zero = phase_events[d, 0]
    one = phase_events[d, 1]
    merged += (mass(zero)+mass(one)-mass(zero | one))/d
require(merged == integrated < haar_reserve, 'one-law merged identity')

# Scope countercontrol to the claim that the extra pair-energy criterion
# contains the entire previously proved incidence-at-most-five class.
outside_primes = (11, 13, 17, 19, 23)
supports = [{3, prime} for prime in outside_primes]
max_incidence = max(sum(prime in support for support in supports)
                    for prime in {3, *outside_primes})
old_class_moduli = [3, 9, 27, 5, 7] + [3**e * prime**h
                                  for prime in outside_primes
                                  for e in (1, 2, 3) for h in (1, 2, 3)]
require(len(old_class_moduli) == len(set(old_class_moduli)), 'scope countercontrol labels')
require(max_incidence == 5, 'old class incidence')
pair_energy = sum(F(2, 3**e) for e in (1, 2, 3))*sum(
    F(1, prime**h) for prime in outside_primes for h in (1, 2, 3))
require(pair_energy > F(1, 3), 'raw-pair bound fails')
merged_source_energy = F(26, 27) * (1-prod(1-F(1, prime) for prime in outside_primes))
require(merged_source_energy < F(1, 3) < pair_energy,
        'same-law phase merging strictly improves raw pairs')

result = {
    'scope': 'Exact finite controls for the retained-phase reserve and merged functional; not Lean verification.',
    'pure_Haar_floor': str(pure_floor),
    'mixed_source_ceiling': str(mixed_ceiling),
    'source_reserve': str(source_reserve),
    'Haar_reserve': str(haar_reserve),
    'actual_distinct_cores_checked': len(core_results),
    'actual_core_period': period,
    'minimum_observed_Haar_survival': str(min(x[0] for x in core_results)),
    'minimum_observed_source_survival': str(min(x[1] for x in core_results)),
    'deep_control': {
        'outside_points': len(points), 'original_labels': len(labels),
        'pairwise_incomparable_pairs_checked': len(labels)*(len(labels)-1)//2,
        'collision_free_outside_points': 0, 'literal_full_integer_hole': 2,
        'minimum_retained_modulus': str(min(retained)),
        'maximum_Haar_phase_excess': str(max(phase_costs)),
        'nonuniform_eta_merged_identity': True,
        'nonuniform_eta_integrated_Haar_excess': str(integrated),
    },
    'scope_countercontrol': {
        'moduli': old_class_moduli,
        'phases': 'pure 3^e uses phase0; each 3^e q^h uses B-phase1 and outside-phase0; pure5/7 use phase0',
        'max_global_support_incidence': max_incidence,
        'actual_same_source_pair_energy': str(pair_energy),
        'actual_same_source_merged_energy': str(merged_source_energy),
        'sufficient_threshold': '1/3',
        'pair_energy_below_threshold': False,
    },
}
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path)
args = parser.parse_args()
if args.output is not None:
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
print('PASS: reserves, 130 actual cores, 143-point deep collision control, one-law merge, scope countercontrol')
