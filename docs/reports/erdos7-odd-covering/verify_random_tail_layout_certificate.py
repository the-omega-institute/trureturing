#!/usr/bin/env python3
"""Evaluate a rational distribution of genuine randomly extended layouts.

Python 3.9+ standard library only. This checks a pointwise LOWER bound on
Gamma for every probability supported on the specified complete survivors.
It does not compute an upper bound or assert a minimax optimum. All layout
scores are reconstructed from residues; no saved solver matrix is trusted.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
import argparse
from fractions import Fraction as F
from itertools import product
import json
from math import gcd, isqrt, lcm, prod
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def integer(value, description):
    require(type(value) is int, description + ' must be an integer')
    return value


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def pure_residue(p, e):
    return (p**(e - 1) - 1) // (p - 1)


def pure_equilibrium(p, height):
    """Exact equal-potential construction on the actual one-dead-branch tree."""
    full = critical = F(2 * height + 1)
    steps = [{'depth': height, 'full_cost': str(full), 'critical_cost': str(critical)}]
    for e in range(height - 1, 0, -1):
        inverse_sum = F(p - 2) / full + 1 / critical
        parallel = 1 / inverse_sum
        full_mass = 1 / (full * inverse_sum)  # Mass of EACH full child.
        critical_mass = 1 / (critical * inverse_sum)
        require((p - 2) * full_mass + critical_mass == 1,
                'critical-node child probabilities do not sum to one')
        require(full_mass * full == critical_mass * critical == parallel,
                'critical-node potentials are not equal')
        full, critical = F(2 * e + 1) + full / p, F(2 * e + 1) + parallel
        steps.append({'depth': e, 'full_cost': str(full), 'critical_cost': str(critical),
                      'each_full_child_mass': str(full_mass),
                      'critical_child_mass': str(critical_mass),
                      'equal_child_potential': str(parallel)})
    inverse_sum = F(p - 2) / full + 1 / critical
    root_full_mass, root_critical_mass = 1 / (full * inverse_sum), 1 / (critical * inverse_sum)
    require((p - 2) * root_full_mass + root_critical_mass == 1,
            'root probabilities do not sum to one')
    require(root_full_mass * full == root_critical_mass * critical == 1 / inverse_sum,
            'root child potentials differ')
    value = 1 + 1 / inverse_sum
    return {'prime': p, 'height': height, 'bottom_up_steps': steps,
            'each_full_root_mass': str(root_full_mass),
            'critical_root_mass': str(root_critical_mass), 'potential': str(value)}


def rectangle_weights(factors, height, divisors, exponent_of):
    """Two independent finite sums reconstruct all lifted cofactor pairs."""
    weights = []
    local_rows = []
    for p, cap in factors:
        length = height - cap
        single = sum((F(1, p**t) for t in range(length + 1)), F(0))
        both = sum((F(2*t + 1, p**t) for t in range(length + 1)), F(0))
        counted = sum((F(1, p**max(t, u))
                       for t in range(length + 1) for u in range(length + 1)), F(0))
        require(both == counted and both >= single**2, 'shared-tail second moment mismatch')
        require(2 * cap * single + both == sum((F(2*e + 1, p**(e - cap))
                 for e in range(cap, height + 1)), F(0)), 'coherent-specialization identity failed')
        local_rows.append({'prime': p, 'cap': cap, 'extra_height': length,
                           'one_capped': str(single), 'both_capped': str(both)})
    for d in divisors:
        row = []
        for e in divisors:
            value = F(1)
            for j, (p, cap) in enumerate(factors):
                a, b = exponent_of[d][j], exponent_of[e][j]
                if a == cap and b == cap:
                    value *= F(local_rows[j]['both_capped'])
                elif a == cap or b == cap:
                    value *= F(local_rows[j]['one_capped'])
            row.append(value)
        weights.append(row)
    index = {d: i for i, d in enumerate(divisors)}
    full_exponents = list(product(range(height + 1), repeat=len(factors)))
    grouped = [[F(0) for _ in divisors] for _ in divisors]
    for u in full_exponents:
        du = prod(p**min(e, cap) for (p, cap), e in zip(factors, u))
        for v in full_exponents:
            dv = prod(p**min(e, cap) for (p, cap), e in zip(factors, v))
            probability = F(1, prod(p**max(max(a-cap, 0), max(b-cap, 0))
                                     for (p, cap), a, b in zip(factors, u, v)))
            grouped[index[du]][index[dv]] += probability
    require(grouped == weights, 'direct enumeration of all fine divisor pairs differs')
    denominator = lcm(*(value.denominator for row in weights for value in row))
    matrix = [[int(value * denominator) for value in row] for row in weights]
    require(all(F(value, denominator) == weights[i][j]
                for i, row in enumerate(matrix) for j, value in enumerate(row)),
            'integer weight matrix is not exact')
    return matrix, denominator, local_rows, len(full_exponents)


def evaluate_certificate_inputs(data):
    height = integer(data['full_height'], 'full height')
    require(height >= 1, 'full height must be positive')
    factors = [tuple(row) for row in data['core_factors']]
    require(factors and all(len(row) == 2 for row in factors), 'invalid core factors')
    for p, cap in factors:
        integer(p, 'core prime'); integer(cap, 'core cap')
        require(is_prime(p) and 1 <= cap <= height, 'invalid prime or height cap')
    require(len({p for p, _ in factors}) == len(factors), 'repeated core prime')
    all_primes = data['full_prime_support']
    require(all(type(p) is int and is_prime(p) for p in all_primes), 'invalid full prime support')
    require(all_primes == sorted(set(all_primes)), 'full prime support is not sorted and unique')
    require({p for p, _ in factors} <= set(all_primes), 'core support is not in full support')
    outside = [p for p in all_primes if p not in {q for q, _ in factors}]
    require(all(p >= 3 for p in outside), 'pure-tree construction requires odd primes')
    core = prod(p**cap for p, cap in factors)
    exponent_of = {prod(p**e for (p, _), e in zip(factors, exponents)): exponents
                   for exponents in product(*(range(cap + 1) for _, cap in factors))}
    divisors = sorted(exponent_of)
    require(data['core_divisor_order'] == divisors, 'layout divisor order mismatch')
    residues = {}
    for d, a in data['core_forbidden_residues']:
        integer(d, 'core divisor'); integer(a, 'forbidden residue')
        require(d not in residues and d > 1 and 0 <= a < d, 'invalid/repeated forbidden residue')
        residues[d] = a
    require(set(residues) == set(divisors) - {1}, 'core forbidden family is incomplete')
    survivors = [x for x in range(core) if all(x % d != a for d, a in residues.items())]
    require(survivors, 'core survivor set is empty')

    matrix, matrix_denominator, local_rows, fine_count = rectangle_weights(
        factors, height, divisors, exponent_of)
    mass_denominator = integer(data['mass_denominator'], 'probability denominator')
    require(mass_denominator > 0, 'probability denominator must be positive')
    layouts = data['layout_rows']
    total_mass = 0
    # The class incidence is constructed from the actual residues, independently
    # of the search program's saved score rows or survivor list.
    incidence = []
    for d in divisors:
        classes = {}
        for j, x in enumerate(survivors):
            classes.setdefault(x % d, []).append(j)
        incidence.append(classes)
    potentials = [0] * len(survivors)
    for row in layouts:
        require(type(row) is list and len(row) == len(divisors) + 1, 'invalid layout row')
        mass = integer(row[0], 'layout numerator')
        require(mass > 0, 'layout numerator must be positive')
        total_mass += mass
        hits = [[] for _ in survivors]
        for i, (d, residue) in enumerate(zip(divisors, row[1:])):
            integer(residue, 'test residue')
            require(0 <= residue < d, 'test residue is outside its divisor')
            for j in incidence[i].get(residue, ()):
                hits[j].append(i)
        for j, active in enumerate(hits):
            value = sum(matrix[i][i] for i in active)
            value += 2 * sum(matrix[i][k] for pos, i in enumerate(active) for k in active[pos + 1:])
            potentials[j] += mass * value
    require(total_mass == mass_denominator, 'layout probabilities do not sum to one')
    potential_denominator = mass_denominator * matrix_denominator
    lower = F(min(potentials), potential_denominator)
    require(lower >= 1, 'the divisor-one contribution is missing')

    outside_rows = []
    outside_factor = F(1)
    for p in outside:
        for e in range(1, height + 1):
            a = pure_residue(p, e)
            require(a == sum(p**j for j in range(e - 1)), 'pure prefix formula mismatch')
            require(0 <= a < p**e and (-1-a) % p**e != 0, 'pure class covers witness')
            for k in range(1, e):
                require((a - pure_residue(p, k)) % p**k != 0, 'pure forbidden prefixes overlap')
        row = pure_equilibrium(p, height)
        outside_rows.append(row)
        outside_factor *= F(row['potential'])
    full_lower = lower * outside_factor
    target = F(data['comparison_target'])

    # A complete family exists with the stated core and pure constraints.
    # Every remaining nonunit divisor uses (witness+1) mod d, which excludes
    # the witness only if d divides 1. No enormous divisor list is needed.
    outside_modulus = prod(p**height for p in outside)
    full_modulus = prod(p**height for p in all_primes)
    witness = outside_modulus * (((survivors[0]+1) * pow(outside_modulus, -1, core)) % core) - 1
    witness %= full_modulus
    require(witness % core == survivors[0] and (witness+1) % outside_modulus == 0,
            'complete-family CRT witness failed')
    require(all(witness % d != a for d, a in residues.items()), 'core class covers witness')
    require(all(witness % p**e != pure_residue(p, e)
                for p in outside for e in range(1, height + 1)), 'pure class covers witness')

    return {'core_modulus': core, 'core_survivor_count': len(survivors),
            'layout_count': len(layouts), 'total_probability_numerator': total_mass,
            'coarse_divisor_count': len(divisors), 'fine_core_divisor_count': fine_count,
            'random_tail_domain_cardinality': prod(p**(height-cap) for p, cap in factors),
            'local_lift_weights': local_rows, 'weight_matrix_denominator': matrix_denominator,
            'potential_common_denominator': potential_denominator,
            'core_potentials': [[x, value] for x, value in zip(survivors, potentials)],
            'minimum_core_potential': str(lower),
            'minimizing_core_residues': [x for x, value in zip(survivors, potentials) if value == min(potentials)],
            'outside_equilibria': outside_rows, 'outside_potential_product': str(outside_factor),
            'full_pointwise_lower_bound': str(full_lower),
            'comparison_target': str(target), 'target_minus_lower_bound': str(target-full_lower),
            'lower_bound_exceeds_target': full_lower > target,
            'full_modulus': str(full_modulus),
            'complete_family_size': (height+1)**len(all_primes)-1,
            'complete_family_survivor_witness': str(witness),
            'scope': 'Gamma lower bound for every supported law; no upper bound or minimax optimality claim'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', default=str((Path(__file__).resolve().parent / 'certificates/random_tail_layout_certificate.json')))
    args = parser.parse_args()
    data = json.loads(read_artifact_text(Path(args.certificate)), object_pairs_hook=unique_object)
    require(data.get('schema') == 'erdos7-random-tail-layout-certificate-v1', 'wrong certificate schema')
    expected = evaluate_certificate_inputs(data)
    require(data['verified_result'] == expected, 'fixed result differs from exact reconstruction')
    lower = F(expected['full_pointwise_lower_bound'])
    print('Verified all ' + str(expected['core_survivor_count']) + ' actual core points and ' +
          str(expected['layout_count']) + ' rational layout probabilities.')
    print('Pointwise Gamma lower bound = ' + format(float(lower), '.12f') +
          '; comparison target = ' + str(expected['comparison_target']) + '.')
    print('This is a lower-bound certificate evaluator, not a Gamma upper bound or a minimax optimum.')


if __name__ == '__main__':
    main()
