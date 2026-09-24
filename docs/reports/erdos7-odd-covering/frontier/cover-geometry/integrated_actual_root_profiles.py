#!/usr/bin/env python3
"""Exact actual-AP counterexamples and consumers for integrated root profiles."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
from itertools import combinations, product
import json
from math import prod
from pathlib import Path

P = (3, 5, 7, 11, 13, 17, 19)
Q = P[1:]
L = P[3:]
FULL = (1 << len(Q))-1
B5 = F(19132074022251234990036997833948759259,
       18473247078046657922374787501704265625)
S0 = F(65869, 378675)
TARGET = F(565, 51)
CHECKS = {}


def check(name, condition):
    if name in CHECKS or not condition:
        raise RuntimeError(name)
    CHECKS[name] = True


def crt(congruences):
    modulus = prod(m for m, _ in congruences)
    residue = sum(a*(modulus//m)*pow(modulus//m, -1, m)
                  for m, a in congruences) % modulus
    return modulus, residue


def mask_of(primes):
    return sum(1 << Q.index(p) for p in primes)


def polynomials(weights):
    @lru_cache(None)
    def phi(mask):
        if not mask:
            return F(1)
        bit = mask & -mask
        answer = phi(mask ^ bit)
        sub = mask
        while sub:
            if sub & bit:
                answer -= weights.get(sub, F(0))*phi(mask ^ sub)
            sub = (sub-1) & mask
        return answer
    return {mask: phi(mask) for mask in range(FULL+1)}


def matches(x, row):
    return x % row[0] == row[1]


# Thirteen actual, irredundant originals; there are no pure originals.
late_supports = tuple(s for k in (2, 3, 4) for s in combinations(L, k))
old = [(prod(s), len(s)-2) for s in late_supports]
thirteen = [(15, 0), (45, 36)]+old
check('thirteen_distinct_odd_numerical_labels',
      len({m for m, _ in thirteen}) == 13
      and all(m > 1 and m % 2 for m, _ in thirteen))
late_period = prod(L)
period13 = 45*late_period
witness13 = [crt(((9, 3), (5, 0))+tuple((p, 3) for p in L))[1],
             crt(((9, 0), (5, 1))+tuple((p, 3) for p in L))[1]]
for s in late_supports:
    witness13.append(crt(((9, 1), (5, 3))+
                        tuple((p, len(s)-2 if p in s else 3) for p in L))[1])
for i, witness in enumerate(witness13):
    check(f'thirteen_irredundant_{i}',
          [j for j, row in enumerate(thirteen) if matches(witness, row)] == [i])

old_weights = {mask_of(s): F(1, prod(s)) for s in late_supports}
phi_old = polynomials(old_weights)[FULL]
sum_pairs = sum((F(1, prod(s)) for s in combinations(L, 2)), F(0))
sum_triples = sum((F(1, prod(s)) for s in combinations(L, 3)), F(0))
check('old_polynomial_independent_expansion',
      phi_old == 1-sum_pairs-sum_triples+F(2, late_period) == F(44801, 46189))
late_count = sum(xs.count(0) < 2 and xs.count(1) < 3 and xs != (2, 2, 2, 2)
                 for xs in product(*(range(p) for p in L)))
check('old_actual_46189_assignments',
      F(late_count, late_period) == 1-sum_pairs+sum_triples-F(1, late_period)
      == F(44918, 46189))
root_count = sum(not any(matches(x, row) for row in thirteen[:2]) for x in range(45))
check('root_actual_45_assignments', root_count == 41)

profiles13 = []
for active, residues in ((0, [1, 2, 4, 5, 7, 8]), (1, [3, 6]), (2, [0])):
    weights = dict(old_weights)
    weights[mask_of((5,))] = F(active, 5)
    phi = polynomials(weights)
    for mask, value in phi.items():
        check(f'thirteen_profile_{active}_subset_{mask}', value > 0)
    check(f'thirteen_profile_{active}_factorization', phi[FULL] == (1-F(active, 5))*phi_old)
    local_collision = F(1, 5) if active == 2 else F(0)
    check(f'thirteen_profile_{active}_dominates_collision', phi[FULL] >= max(F(0), S0-local_collision))
    profiles13.append({'root_residues_mod9': residues, 'mass': F(len(residues), 9),
                       'scope_union_probabilities': weights, 'all64_polynomials': phi,
                       'lower': phi[FULL]})
s13 = sum((p['mass']*p['lower'] for p in profiles13), F(0))
omega13 = F(1, 9)*F(1, 5)
collision_margin = S0-F(51, 310)*B5
r13 = 5+B5/s13
actual13 = F(root_count, 45)*F(late_count, late_period)
check('thirteen_integrated_lower', s13 == F(1836841, 2078505))
check('thirteen_actual_survival', actual13 == F(1841638, 2078505))
check('thirteen_bound_valid_and_crosses', 0 < s13 <= actual13 and r13 < TARGET)
check('thirteen_old_collision_criterion_fails', omega13 > collision_margin)
check('thirteen_old_collision_query_above_target', 5+B5/(S0-omega13) > TARGET)

# Twelve actual irredundant originals cover the entire positive-mass root fibre.
twelve = [(3, 0), (5, 0), (7, 0)]
for a in (1, 2, 3):
    twelve.extend((crt(((3**a, 1), (5, a))), crt(((3**a, 1), (7, a))),
                   crt(((3**a, 1), (5, 4), (7, a+3)))))
check('twelve_distinct_odd_numerical_labels',
      len({m for m, _ in twelve}) == 12 and all(m > 1 and m % 2 for m, _ in twelve))
witness12 = {}
survivor12 = []
for x in range(945):
    hits = [i for i, row in enumerate(twelve) if matches(x, row)]
    if not hits:
        survivor12.append(x)
    if len(hits) == 1:
        witness12.setdefault(hits[0], x)
for i in range(12):
    check(f'twelve_irredundant_{i}', i in witness12)
check('twelve_actual_survivor_count', len(survivor12) == 312)
check('twelve_positive_root_fibre_empty',
      not any(x % 27 == 1 for x in survivor12))
root_classes = {j: [r for r in range(27) if r % 3 and
                   sum(r % (3**a) == 1 for a in (1, 2, 3)) == j] for j in range(4)}
profiles12 = []
for j in range(4):
    root_mass = F(len(root_classes[j]), 18)
    count = 0
    for r, x5, x7 in product(root_classes[j], range(1, 5), range(1, 7)):
        _, x = crt(((27, r), (5, x5), (7, x7)))
        count += not any(matches(x, row) for row in twelve)
    actual = F(count, len(root_classes[j])*24)
    weights = {mask_of((5,)): F(j, 4), mask_of((7,)): F(j, 6), mask_of((5, 7)): F(j, 24)}
    phi = polynomials(weights)
    valid = all(v > 0 for v in phi.values())
    lower = phi[FULL] if valid else F(0)
    check(f'twelve_fibre_{j}_closed_count', actual == F((4-j)*(6-j)-j, 24))
    check(f'twelve_fibre_{j}_profile', lower == actual)
    profiles12.append({'root_residues_mod27': root_classes[j], 'mass': root_mass,
                       'all64_polynomials': phi, 'all64_positive': valid,
                       'lower': lower, 'actual_survival': actual})
check('twelve_root_profile_masses', [p['mass'] for p in profiles12] == [F(1, 2), F(1, 3), F(1, 9), F(1, 18)])
check('twelve_deep_fibre_has_positive_source_mass', profiles12[3]['mass'] == F(1, 18))
check('twelve_deep_fibre_zero_polynomial', profiles12[3]['all64_polynomials'][mask_of((5, 7))] == 0)
s12 = sum((p['mass']*p['lower'] for p in profiles12), F(0))
check('twelve_integrated_exact', s12 == F(312, 432) == F(13, 18))

# Two disjoint ternary prefixes: averaging inputs overstates true survival.
jensen_rows = [(15, 0), (21, 1)]
actual_jensen = F(sum(not any(matches(x, row) for row in jensen_rows) for x in range(105)), 105)
average_phi = sum(((1-(F(1, 5) if r == 0 else 0))*(1-(F(1, 7) if r == 1 else 0)) for r in range(3)), F(0))/3
phi_average = (1-F(1, 15))*(1-F(1, 21))
check('jensen_actual_is_average_of_profiles', actual_jensen == average_phi == F(31, 35))
check('jensen_averaged_inputs_overstate', phi_average == F(8, 9) and phi_average-average_phi == F(1, 315))

result = {
    'scope': 'Actual fixed AP families; conditional integrated certificate and two method refutations, not unrestricted Erdos7.',
    'B5': B5, 'target': TARGET, 'old_s0': S0, 'old_collision_margin': collision_margin,
    'thirteen': {'originals_modulus_residue': thirteen, 'irredundancy_witnesses': witness13,
                 'period': period13, 'profiles': profiles13, 'integrated_lower': s13,
                 'actual_Haar_survival': actual13, 'collision': omega13,
                 'complete_query_bound': r13, 'complete_query_bound_decimal': float(r13)},
    'twelve': {'originals_modulus_residue': twelve, 'irredundancy_witnesses': witness12,
              'period': 945, 'survivor_count': len(survivor12), 'profiles': profiles12,
              'pure_conditioned_survival': s12, 'actual_Haar_survival': F(len(survivor12), 945)},
    'jensen': {'originals_modulus_residue': jensen_rows, 'actual_Haar_survival': actual_jensen,
               'mean_profile': average_phi, 'profile_of_means': phi_average,
               'overstatement': phi_average-average_phi},
    'refuted_claims': ['Every actual root fibre has positive survivor mass under arbitrary nested root prefixes.',
                       'Applying the support polynomial after averaging actual root loads always lower-bounds survival.'],
    'limits': 'No universal integrated lower bound, root-reweighting theorem, general prime-count reduction or Lean verification.',
    'checks': CHECKS, 'passed_checks': len(CHECKS)}


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value).__name__)


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
args = parser.parse_args()
args.output.write_text(json.dumps(result, indent=2, default=encode)+'\n')
print(json.dumps({'passed_checks': len(CHECKS), 'thirteen_integrated_lower': s13,
                  'thirteen_query_bound': float(r13), 'thirteen_collision': omega13,
                  'twelve_survivor_count': len(survivor12), 'twelve_pure_conditioned_survival': s12,
                  'jensen_overstatement': phi_average-average_phi}, indent=2, default=encode))
print(hashlib.sha256(args.output.read_bytes()).hexdigest())
