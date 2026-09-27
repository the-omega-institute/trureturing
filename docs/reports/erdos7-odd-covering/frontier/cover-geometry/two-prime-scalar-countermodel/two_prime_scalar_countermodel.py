#!/usr/bin/env python3
"""Exact actual-phase countermodel to scalar-only preservation of a fixed law."""
from fractions import Fraction as F
from itertools import product
from math import prod
import json

def require(condition, message):
    if not condition:
        raise ValueError(message)

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def crt(coordinates):
    result, modulus = 0, 1
    for residue, new_modulus in coordinates:
        result += modulus * (((residue - result) * pow(modulus, -1, new_modulus)) % new_modulus)
        modulus *= new_modulus
        result %= modulus
    return result, modulus

K, q, r = 3**6 * 5**2, 23, 29
D = divisors(K)
nonunit = D[1:]
require(len(nonunit) == 20, 'Old nonunit divisor count')
classes = []
for d in nonunit:
    classes.append(dict(kind='old', residue=0, modulus=d))
classes.extend([dict(kind='pure_q', residue=0, modulus=q), dict(kind='pure_r', residue=0, modulus=r)])
for j, d in enumerate(nonunit, 1):
    residue, modulus = crt([(1, d), (j, q)])
    classes.append(dict(kind='q_only', residue=residue, modulus=modulus))
    residue, modulus = crt([(1, d), (j, r)])
    classes.append(dict(kind='r_only', residue=residue, modulus=modulus))
leftover = list(product(range(21, q), range(21, r)))
require(len(leftover) == 16, 'Residual rectangle size')
for d, (u, v) in zip(D, leftover):
    coordinates = ([(1, d)] if d > 1 else []) + [(u, q), (v, r)]
    residue, modulus = crt(coordinates)
    classes.append(dict(kind='mixed', residue=residue, modulus=modulus))
require(len(classes) == 78, 'Original class inventory')
require(len({c['modulus'] for c in classes}) == len(classes), 'Distinct numerical moduli')
require(all(c['modulus'] > 1 and c['modulus'] % 2 for c in classes), 'Odd nontrivial moduli')
require(all(1 % c['modulus'] != c['residue'] for c in classes if c['kind'] == 'old'), 'Old law is on actual survivors')
counts = {'q_only': 0, 'r_only': 0, 'mixed': 0, 'q_r_overlap': 0, 'uncovered': 0}
for u, v in product(range(1, q), range(1, r)):
    x, _ = crt([(1, K), (u, q), (v, r)])
    hit = {c['kind'] for c in classes if x % c['modulus'] == c['residue']}
    require(not ({'old', 'pure_q', 'pure_r'} & hit), 'Conditioned support')
    for kind in ['q_only', 'r_only', 'mixed']:
        counts[kind] += kind in hit
    counts['q_r_overlap'] += {'q_only', 'r_only'} <= hit
    counts['uncovered'] += not hit
require(counts == {'q_only': 560, 'r_only': 440, 'mixed': 16, 'q_r_overlap': 400, 'uncovered': 0}, 'Exact fibre counts')
alpha, beta, gamma = F(20, 22), F(20, 28), F(16, 22*28)
require((1-alpha)*(1-beta)-gamma == 0, 'Conditional-fibre identity')
witness, full_period = crt([(2, K), (1, q), (1, r)])
require(all(witness % c['modulus'] != c['residue'] for c in classes), 'Actual full family remains noncovering')
seed_A, seed_Lambda = F(70874, 3375), 455625
require(F(20) < seed_A and K <= seed_Lambda, 'Published scalar hypotheses')
# Optional padding gives seven actual old prime coordinates without changing the kill.
padding = [127, 131, 137, 139, 149]
padding_factor = prod((F(p, p-1) for p in padding), start=F(1))
padded_R = 21 * padding_factor - 1
padded_cap = K * padding_factor
require(padded_R < seed_A and padded_cap < seed_Lambda, 'Seven-coordinate scalar hypotheses')
# Equal scalar data and equal separate loads do not fix the shared overlap.
paired = {}
for r_old_phase in (1, 2):
    overlap = F(0)
    q_mean = F(0)
    r_mean = F(0)
    for old in (1, 2):
        aq = F(int(old == 1), q-1)
        br = F(int(old == r_old_phase), r-1)
        q_mean += aq / 2
        r_mean += br / 2
        overlap += aq * br / 2
    q_residue, q_modulus = crt([(1, 3), (1, q)])
    r_residue, r_modulus = crt([(r_old_phase, 3), (1, r)])
    paired[str(r_old_phase)] = {
        'old_law': 'uniform on 1 and 2 modulo 3',
        'old_original': {'modulus': 3, 'residue': 0},
        'pure_originals': [{'modulus': q, 'residue': 0}, {'modulus': r, 'residue': 0}],
        'mixed_originals': [{'modulus': q_modulus, 'residue': q_residue},
                            {'modulus': r_modulus, 'residue': r_residue}],
        'q_mean': str(q_mean), 'r_mean': str(r_mean), 'overlap': str(overlap)}
require(paired['1']['q_mean'] == paired['2']['q_mean'] and paired['1']['r_mean'] == paired['2']['r_mean'], 'Paired loads equal')
require(paired['1']['overlap'] == str(F(1, 2*(q-1)*(r-1))) and paired['2']['overlap'] == '0', 'Paired overlap separation')
result = {
    'kind': 'actual_phase_countermodel_to_preserving_an_arbitrary_fixed_core_law',
    'K': K, 'q': q, 'r': r,
    'old_law': 'delta at residue 1',
    'R': '20', 'density_cap': str(K),
    'seed_A': str(seed_A), 'seed_density_cap': seed_Lambda,
    'period': full_period, 'original_class_count': len(classes),
    'conditioned_product_cell_count': (q-1)*(r-1),
    'counts': counts,
    'alpha': str(alpha), 'beta': str(beta),
    'alpha_beta': str(alpha*beta), 'mixed_residual': str(gamma),
    'actual_product_live_mass': '0',
    'full_original_family_uncovered_integer': witness,
    'seven_old_prime_padding': {
        'additional_original_classes': [{'modulus': p, 'residue': 0} for p in padding],
        'old_law': 'delta_1 on K times independent uniform nonzero coordinates on the five added primes',
        'R': str(padded_R), 'density_cap': str(padded_cap),
        'scope': 'Separate padded instance with 83 original classes, obtained by adding these five classes to the 78-class base instance.'},
    'original_classes': classes,
    'paired_old_core_3': paired,
    'scope': 'No claim about every admissible core law, the report462 selected law, first-seven support, or an integer covering.'
}
print(json.dumps(result, indent=2))
