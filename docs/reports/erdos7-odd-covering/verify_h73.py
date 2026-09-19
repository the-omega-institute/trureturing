#!/usr/bin/env python3
"""Verify a finite counterexample to the proposed H73 measure bound.

Python >= 3.8 standard library only. All checks remain active under python -O.
The certificate supplies congruences and nonnegative rational LP dual weights;
no numerical solver or trusted floating-point result is used.
Original repository experiment; the mathematical proof and scope are in
Problems/erdos-7-odd-covering-systems.md, Evidence / H73.

For a full divisor d and d0=gcd(d,4725), each supported d0-coset has at
most prod_core p**(v_p(d)-v_p(d0)) * prod_outside N_p(v_p(d)) refinements,
where N_p(e)=p**e-sum(p**i for i in range(e)). Pigeonholing a largest
projected coset separately for every d proves the weighted lower bound.
No independence of the measure's coordinates is assumed.
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
from fractions import Fraction
from itertools import product
import json
from math import prod
from pathlib import Path
import sys

HEIGHT = 4
CORE_FACTORS = ((3, 3), (5, 2), (7, 1))
CORE = 4725
TARGET = Fraction(138877, 1000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        require(key not in obj, 'Duplicate JSON object key: ' + key)
        obj[key] = value
    return obj


def integer(value, description):
    require(type(value) is int, description + ' must be an integer')
    return value


def primes():
    return tuple(n for n in range(3, 74, 2)
                 if all(n % k for k in range(2, n)))


def effective_weights():
    """Group the original chi(d)=prod(2*v_p(d)+1) over core primes.

    Enumerate all 125 exponent tuples in [0,4]^3, retaining d0=gcd(d,CORE)
    and dividing each original weight by the number of refined core cosets.
    This independently reconstructs all 24 coefficients used by the LP.
    """
    weights = {}
    for exponents in product(range(HEIGHT + 1), repeat=len(CORE_FACTORS)):
        d0, refinements, original_chi = 1, 1, 1
        for (p, cap), exponent in zip(CORE_FACTORS, exponents):
            truncated = min(cap, exponent)
            d0 *= p ** truncated
            refinements *= p ** (exponent - truncated)
            original_chi *= 2 * exponent + 1
        weights[d0] = weights.get(d0, Fraction(0)) + Fraction(original_chi, refinements)
    return weights


def pure_residue(p, exponent):
    return (p ** (exponent - 1) - 1) // (p - 1)


def verify(certificate_path):
    certificate = json.loads(read_artifact_text(Path(certificate_path), encoding='utf-8'),
                             object_pairs_hook=unique_object)
    require(type(certificate) is dict, 'Certificate must be a JSON object')
    require(set(certificate) == {'core_residues', 'dual'}, 'Unexpected certificate fields')
    require(prod(p ** e for p, e in CORE_FACTORS) == CORE, 'Wrong core factorization')
    all_primes = primes()
    require(len(all_primes) == 20, 'Expected all 20 odd primes through 73')
    outside = tuple(p for p in all_primes if p not in (3, 5, 7))
    weights = effective_weights()
    require(len(weights) == 24 and 1 in weights and CORE in weights,
            'Effective weights must include all 24 core divisors, including 1 and CORE')

    residues = {}
    require(type(certificate['core_residues']) is list, 'core_residues must be a list')
    for row in certificate['core_residues']:
        require(type(row) is list and len(row) == 2, 'Invalid core residue row')
        d = integer(row[0], 'Core divisor')
        residue = integer(row[1], 'Core residue')
        require(d not in residues, 'Repeated core modulus')
        require(d > 1 and 0 <= residue < d, 'Invalid core congruence')
        residues[d] = residue
    require(set(residues) == set(weights) - {1}, 'Must assign every nonunit core divisor')
    survivors = [z for z in range(CORE)
                 if all(z % d != residue for d, residue in residues.items())]
    require(len(survivors) == 791 and 3 in survivors, 'Core survivor check failed')

    dual = {}
    budgets = {d: Fraction(0) for d in weights}
    require(type(certificate['dual']) is list, 'dual must be a list')
    require(len(certificate['dual']) == 182, 'Expected 182 nonzero dual terms')
    for row in certificate['dual']:
        require(type(row) is list and len(row) == 3, 'Invalid dual row')
        d = integer(row[0], 'Dual divisor')
        b = integer(row[1], 'Dual residue')
        require(type(row[2]) is str, 'Dual weight must be an exact rational string')
        value = Fraction(row[2])
        require(d in weights and 0 <= b < d and value > 0, 'Invalid dual coefficient')
        require((d, b) not in dual, 'Repeated dual coefficient')
        dual[d, b] = value
        budgets[d] += value
    for d, budget in budgets.items():
        require(budget <= weights[d], 'Dual budget exceeded at divisor ' + str(d))
    lower = min(sum((dual.get((d, z % d), Fraction(0)) for d in weights), Fraction(0))
                for z in survivors)
    require(lower == Fraction(25730979793, 1000000000), 'Measured dual minimum changed')

    outside_factor = Fraction(1)
    for p in outside:
        factor = Fraction(1)
        for exponent in range(1, HEIGHT + 1):
            modulus = p ** exponent
            a = pure_residue(p, exponent)
            require(0 <= a < modulus and (-1 - a) % modulus != 0,
                    'Outside pure class contains proposed witness')
            for earlier in range(1, exponent):
                require((a - pure_residue(p, earlier)) % (p ** earlier) != 0,
                        'Outside pure classes are not pairwise disjoint')
            allowed = modulus - sum(p ** i for i in range(exponent))
            require(allowed > 0, 'No allowed outside residue')
            factor += Fraction(2 * exponent + 1, allowed)
        outside_factor *= factor

    full_modulus = prod(p ** HEIGHT for p in all_primes)
    outside_modulus = prod(p ** HEIGHT for p in outside)
    witness = outside_modulus * ((4 * pow(outside_modulus, -1, CORE)) % CORE) - 1
    witness %= full_modulus
    require(witness % CORE == 3 and (witness + 1) % outside_modulus == 0,
            'CRT witness failed')

    def assigned_residue(d):
        """One explicit residue for every d>1 dividing the full modulus."""
        require(type(d) is int and d > 1 and full_modulus % d == 0,
                'Not a nonunit divisor of the full modulus')
        if d in residues:
            return residues[d]
        for p in outside:
            for exponent in range(1, HEIGHT + 1):
                if d == p ** exponent:
                    return pure_residue(p, exponent)
        return (witness + 1) % d

    # Check all exceptional cases. Every remaining d uses (witness+1) mod d;
    # equality with witness mod d would force d to divide 1, impossible for d>1.
    exceptional_moduli = set(residues)
    exceptional_moduli.update(p ** e for p in outside for e in range(1, HEIGHT + 1))
    for d in exceptional_moduli:
        require(witness % d != assigned_residue(d), 'Exceptional class covers witness')
    require(witness % full_modulus != assigned_residue(full_modulus),
            'Top modulus class covers witness')
    # Since the assignment includes d=full_modulus, its actual LCM is full_modulus.
    full_lower = lower * outside_factor
    require(lower > 25 and outside_factor > 6, 'Simplified factors failed')
    require(full_lower > 150 and Fraction(150) > TARGET, 'H73 contradiction failed')
    require(full_lower > Fraction(1621563, 10000), 'Sharper rational lower bound failed')
    return {
        'verified': True,
        'full_prime_count': len(all_primes),
        'full_height': HEIGHT,
        'full_modulus': str(full_modulus),
        'full_family_size': (HEIGHT + 1) ** len(all_primes) - 1,
        'full_survivor_witness': str(witness),
        'core_modulus': CORE,
        'core_survivors': len(survivors),
        'effective_weight_count': len(weights),
        'nonzero_dual_terms': sum(value > 0 for value in dual.values()),
        'core_dual_minimum': str(lower),
        'outside_factor': str(outside_factor),
        'full_kappa_lower_bound': str(full_lower),
        'H73_target': str(TARGET),
        'exact_comparison': 'full_kappa_lower_bound > 1621563/10000 > 150 > 138877/1000',
        'scope': 'Counterexample to H73; the explicit survivor prevents a covering of the integers.'
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?',
                        default=str((Path(__file__).resolve().parent / 'certificates/h73_dual.json')))
    args = parser.parse_args()
    try:
        result = verify(args.certificate)
    except (OSError, ValueError, TypeError, ZeroDivisionError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
