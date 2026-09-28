#!/usr/bin/env python3
"""Twelve/thirteen small-prime heads with unrestricted finite large-prime tails.

Only head-only original moduli require ternary height at most one. The seed
is explicitly changed to the actual Haar restriction at head heights that
resolve the whole family. Final reserves are distorted-measure mass, not
full-family Haar density. Uses Chapter33's stated analytic premise; no Lean claim.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import json
from math import factorial, prod
from pathlib import Path


PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43)
CASES = (
    (12, 'fibre_credit_support_shearer.json',
     '726383868162c8c85c79f514ea5e1d944884fd03d65806d3c27fb54251666140',
     'twelve_prime_haar_lower', 100000, 10, F(1, 450), F(1, 750)),
    (13, 'fibre_credit_support_thirteen.json',
     '64799100b5dafbe9991d54acbd41e881c6ed98244f36b2e7e2615bf25e89ec7b',
     'thirteen_prime_haar_lower', 1000000, 12, F(1, 11000), F(1, 100000)),
)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def verify(package):
    cases = []
    for count, filename, pinned, field, cutoff, level, mass, lower in CASES:
        raw = (package / filename).read_bytes()
        need(sha256(raw).hexdigest() == pinned, 'pinned head-density certificate')
        seed = json.loads(raw)
        need(F(seed[field]) > mass and F(seed['no_three_haar_lower']) > mass,
             'both actual head branches have sufficient Haar mass')
        need(cutoff >= 286 and level >= 4 and 3 ** level <= cutoff,
             'all inherited SH11 analytic applicability conditions')
        moment = prod(F(p * (p + 1), (p - 1) ** 2) for p in PRIMES[:count])
        c = F(2 * level ** 2 + 1, 2 * level ** 2 - 1)
        polynomial = sum((F(factorial(7), factorial(7 - j) * level ** j)
                          for j in range(8)), F(0))
        tau = c ** 7 * F(cutoff, (cutoff - 3) ** 2) * polynomial
        loss, reserve = moment * tau, mass - moment * tau
        need(reserve > lower, 'strict remaining distorted-measure mass')
        cases.append(dict(head_count=count, head_seed_file=filename, head_seed_sha256=pinned,
                          reference_head_primes=PRIMES[:count], cutoff=cutoff, level=level,
                          three_to_level=3 ** level, head_mass_floor=str(mass),
                          head_source='Actual Haar restriction H_R|U at full-family head heights',
                          head_joint_Haar_density_cap='1',
                          head_second_moment_upper=str(moment), analytic_product_constant=str(c),
                          integral_polynomial=str(polynomial), tau7=str(tau),
                          complete_tail_loss_upper=str(loss),
                          distorted_survivor_mass_lower=str(reserve),
                          stated_distorted_mass_floor=str(lower), strict_surplus=str(reserve - lower)))
    return dict(scope=__doc__, cases=cases,
                analytic_dependency='Chapter33 SH11 and its Rosser-Schoenfeld/Chapter32 source attribution; not proved by this rational checker',
                boundary='Each family is finite, with distinct odd nonunit numerical moduli. The number of tail primes and all tail-touching exponents are unrestricted finite. Only originals wholly on the small head have v3<=1. These reserves are not full-family Haar density bounds.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.dumps(verify(args.package), sort_keys=True, indent=2) + '\n'
    if args.output is None:
        need(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == json.loads(result),
             'retained tail result agrees with exact replay')
        print(result, end='')
    else:
        args.output.write_text(result)
