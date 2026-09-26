#!/usr/bin/env python3
"""Exact finite certificate for an AH9-interface/coherent-load counterexample.

Ordinary proof obligations are stated in the companion note. This program checks
finite rational sums, actual label inventory and the claimed strict gaps. It does
not reconstruct Report467's source selector or prove a Lean theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import prod, isqrt
import argparse
import json

P = (3, 5, 7, 11, 13, 17, 19)
A = F(70871, 3375)
LAMBDA = F(6075000000000, 7235955529)
MIX = F(2, 5)
THRESHOLD = 32
CURRENT = 23

def require(test, message):
    if not test:
        raise ArithmeticError(message)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    args = parser.parse_args()
    require(all(p > 2 and all(p % k for k in range(2, isqrt(p) + 1)) for p in P + (CURRENT,)), 'primes')
    profiles = tuple(product(range(3), repeat=len(P)))
    old_moduli = tuple(prod(p ** e for p, e in zip(P, v)) for v in profiles)
    full = tuple(CURRENT * d for d in old_moduli if d > 1)
    short = tuple(CURRENT * p for p in P)
    require(len(profiles) == 2187, 'profile inventory')
    require(len(full) == len(set(full)) == 2186, 'full original inventory')
    require(len(short) == len(set(short)) == 7, 'short original inventory')
    require(all(m > 1 and m % 2 for m in full), 'distinct odd originals')
    require(set(short).issubset(full), 'short family included')
    require(all(any(m % k == 0 for k in short) for m in full), 'same union by cylinder containment')
    require(F(2 * len(short), CURRENT) < 1, 'short additive hinge zero')

    probability = first_inf = event_mass = event_first_inf = F(0)
    haar_hinge = event_hinge = F(0)
    actual_hinge = short_hinge = F(0)
    event_profiles = 0
    for v in profiles:
        # v_p=0,1,>=2 are exact Haar cells, independent across old primes.
        mass = prod(F(p - 1, p ** (e + 1)) if e < 2 else F(1, p ** 2)
                    for p, e in zip(P, v))
        d2 = prod(e + 1 for e in v)
        # Conditional tail expectation E(v_p+1 | v_p>=2)=2+p/(p-1).
        dinf = prod(F(e + 1) if e < 2 else F(2) + F(p, p - 1)
                    for p, e in zip(P, v))
        f_full = F(d2 - 1, CURRENT)
        f_short = F(sum(e > 0 for e in v), CURRENT)
        alpha = F(int(any(e > 0 for e in v)), CURRENT)
        h_full = max(F(0), 2 * f_full - 1)
        h_short = max(F(0), 2 * f_short - 1)
        h_actual = max(F(0), 2 * alpha - 1)
        require(h_short == h_actual == 0, 'pointwise zero short/actual hinge')
        probability += mass
        first_inf += mass * dinf
        haar_hinge += mass * h_full
        short_hinge += mass * h_short
        actual_hinge += mass * h_actual
        if d2 >= THRESHOLD:
            event_profiles += 1
            event_mass += mass
            event_first_inf += mass * dinf
            event_hinge += mass * h_full
    require(probability == 1, 'Haar profile partition')
    require(first_inf == prod(F(p, p - 1) for p in P), 'all-height Haar divisor moment')
    require(0 < event_mass < 1 and 0 < MIX < 1, 'full-support mixture')
    r_infty = (1 - MIX) * first_inf + MIX * event_first_inf / event_mass - 1
    density = 1 - MIX + MIX / event_mass
    hinge = (1 - MIX) * haar_hinge + MIX * event_hinge / event_mass
    require(r_infty < A, 'AH9 complete query cap')
    require(density < LAMBDA, 'AH9 density cap')
    require(hinge > 1, 'uncapped hinge exceeds one')
    require(short_hinge == actual_hinge == 0, 'short and actual hinges')
    rational = {
        'A': A, 'Lambda': LAMBDA, 'mixture': MIX,
        'Haar_event_mass': event_mass, 'Haar_infinite_divisor_moment': first_inf,
        'Haar_infinite_divisor_moment_on_event': event_first_inf,
        'Haar_uncapped_hinge': haar_hinge, 'Haar_uncapped_hinge_on_event': event_hinge,
        'R_infty': r_infty, 'A_minus_R_infty': A - r_infty,
        'density_max': density, 'Lambda_minus_density_max': LAMBDA - density,
        'uncapped_hinge': hinge, 'uncapped_hinge_minus_one': hinge - 1,
        'short_additive_hinge': short_hinge, 'actual_union_hinge': actual_hinge,
        'density_min': 1 - MIX,
    }
    result = {
        'scope': 'AH9 scalar/support interface; canonical467 source selection not reconstructed; no irredundancy or whole-cover premise; no Lean claim',
        'old_primes': P, 'current_prime': CURRENT, 'old_height': 2,
        'event_threshold': THRESHOLD, 'valuation_profiles': len(profiles),
        'event_profiles': event_profiles, 'actual_full_labels': len(full),
        'actual_short_labels': len(short), 'old_original_count': 0,
        'old_height_two_period': prod(p ** 2 for p in P),
        'same_union_certificate': 'short subset full; every full zero class is contained in one short zero class by literal modulus divisibility',
        'exact': {key: str(value) for key, value in rational.items()},
        'decimals': {key: float(rational[key]) for key in ('R_infty', 'density_max', 'uncapped_hinge')},
    }
    rendered = json.dumps(result, indent=2, ensure_ascii=False) + '\n'
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as handle:
            handle.write(rendered)
    print(rendered, end='')

if __name__ == '__main__':
    main()
