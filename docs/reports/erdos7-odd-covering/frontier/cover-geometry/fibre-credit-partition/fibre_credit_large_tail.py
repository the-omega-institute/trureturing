"""Existing joint-moment tail bound applied to the eleven-prime density.

There are at most11 actual support primes at most100000. Only originals
wholly on this head require v3(m)<=1. All tail-touching originals may have
arbitrary old and new finite exponents. The entire original family is
finite, but the number of tail primes has no uniform bound.
The final reserve is distorted-measure mass, not full Haar density.
Ordinary proof using Chapter33's analytic premise; no new Lean claim.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import factorial, prod
from pathlib import Path
import argparse
import json


SEED_HASH = '2b6a70b1adda2bea55873433271367cb3b9ce7deb1c03c9f111c06015c290806'
PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def verify(package):
    raw = (package / 'fibre_credit_pure_extension.json').read_bytes()
    need(sha256(raw).hexdigest() == SEED_HASH, 'pinned head density certificate')
    seed = json.loads(raw)
    mass, density = F(1, 700), F(1)
    need(F(seed['arbitrary_nonternary_heights']['full_haar_survivor_lower']['exact']) > mass
         and F(seed['without3_empty_core']['haar_survivor_lower']) > mass,
         'both head branches have strictly sufficient Haar mass')
    cutoff, level = 100000, 10
    need(cutoff >= 286 and level >= 4 and 3**level <= cutoff, 'SH11 applicability')
    c = F(2*level**2 + 1, 2*level**2 - 1)
    moment = prod(F(p*(p + 1), (p - 1)**2) for p in PRIMES)
    polynomial = sum((F(factorial(7), factorial(7 - j)*level**j)
                      for j in range(8)), F(0))
    allowance = c**7 / cutoff * F(cutoff, cutoff - 3)**2 * polynomial
    loss = density * moment * allowance
    reserve = mass - loss
    need(moment == F(61036374269, 1970749440), 'worst eleven-prime Haar moment')
    need(polynomial == F(305593, 125000), 'positive integral comparison polynomial')
    need(reserve == F(1663915295841259580268266967, 2699162034910424804010207948800),
         'complete tail comparison reserve')
    need(reserve > F(1, 2000), 'strict remaining distorted mass')
    return {'scope': __doc__, 'head_seed_sha256': SEED_HASH,
            'reference_head_primes': PRIMES, 'cutoff': cutoff, 'level': level,
            'three_to_level': 3**level, 'analytic_product_constant': str(c),
            'head_source': 'Actual Haar restriction H|U at full-family head heights',
            'head_mass_floor': str(mass), 'head_joint_haar_cap': str(density),
            'head_second_moment_upper': str(moment), 'integral_polynomial': str(polynomial),
            'tau7': str(allowance), 'complete_tail_loss_upper': str(loss),
            'distorted_survivor_mass_lower': str(reserve),
            'distorted_survivor_mass_lower_decimal': float(reserve),
            'surplus_over_1_over_2000': str(reserve - F(1, 2000)),
            'analytic_dependency': 'Chapter33 SH11, with Rosser-Schoenfeld/source attribution; not proved by this rational computation',
            'boundary': 'No all-depth head query norm is assumed. The head-height condition applies only to head-only originals. Arbitrary deeper head exponents in tail originals enter the existing joint Haar moment. Positive mass gives an uncovered integer; this weighted reserve is not claimed as its natural-density lower bound.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    output = json.dumps(verify(args.package), sort_keys=True, indent=2) + '\n'
    if args.output is None:
        print(output, end='')
    else:
        args.output.write_text(output)
