#!/usr/bin/env python3
"""Exact finite diagnostics for factorial congruence and Robin-source offsets.

Python 3.9+, standard library only, runnable from any working directory.
These finite identities do not certify Mertens, a uniform asymptotic, Robin,
RH, or a Lean theorem. No floating point enters a sign or equality check.
"""

import argparse
from collections import defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from math import factorial, gcd, isqrt, prod
from pathlib import Path


@lru_cache(maxsize=None)
def factors(n):
    assert n >= 1
    original, found, p = n, {}, 2
    while p*p <= n:
        while n % p == 0:
            found[p] = found.get(p, 0)+1
            n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        found[n] = 1
    assert prod(p**a for p, a in found.items()) == original
    assert all(all(p % d for d in range(2, isqrt(p)+1)) for p in found)
    return found


def valuation(n, p):
    assert n != 0
    n, exponent = abs(n), 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def local_z(p, a):
    return Fraction(p**(a+1)-1, p**a*(p-1))


def z_from_factors(decomposition):
    return prod((local_z(p, a) for p, a in decomposition.items()), start=Fraction(1))


def low_z(n, m):
    return prod((local_z(p, a) for p, a in factors(n).items() if p <= m),
                start=Fraction(1))


def primes_through(n):
    return [p for p in range(2, n+1) if len(factors(p)) == 1 and factors(p).get(p) == 1]


def factorial_factors(m):
    return {p: sum(m//p**a for a in range(1, m+1)) for p in primes_through(m)}


def delta(m):
    return prod((1-Fraction(1, p**(a+1)) for p, a in factorial_factors(m).items()),
                start=Fraction(1))


def wire(value):
    return [value.numerator, value.denominator]


def local_checks():
    limit, pairs, signed_pairs = 256, 0, 0
    for n in range(1, limit+1):
        direct = sum((Fraction(1, d) for d in range(1, n+1) if n % d == 0), Fraction())
        assert direct == z_from_factors(factors(n))
    rows = []
    for m in range(2, 8):
        modulus, groups = factorial(m), defaultdict(list)
        for n in range(1, limit+1):
            groups[n % modulus].append(n)
        bound = delta(m)
        lowest, highest, count, signed_count = Fraction(1), Fraction(1), 0, 0
        for residue, group in groups.items():
            for a in group:
                for b in group:
                    ratio = low_z(a, m)/low_z(b, m)
                    assert bound <= ratio <= 1/bound
                    lowest, highest = min(lowest, ratio), max(highest, ratio)
                    count += 1
                for b in groups.get((-residue) % modulus, ()):
                    ratio = low_z(a, m)/low_z(b, m)
                    assert bound <= ratio <= 1/bound
                    signed_count += 1
        pairs += count
        signed_pairs += signed_count
        rows.append({'m': m, 'modulus': modulus, 'delta': wire(bound),
                     'minimum_low_ratio': wire(lowest), 'maximum_low_ratio': wire(highest),
                     'ordered_same_residue_pairs': count, 'ordered_opposite_residue_pairs': signed_count})
    return {'complete_factorization_and_direct_divisor_range': [1, limit],
            'same_residue_pairs': pairs, 'opposite_residue_pairs': signed_pairs, 'rows': rows}


def truncation_checks():
    rows = []
    for m in range(2, 121):
        fac = factorial_factors(m)
        assert prod(p**a for p, a in fac.items()) == factorial(m)
        loss = sum((Fraction(1, p**(a+1)) for p, a in fac.items()), Fraction())
        low = sum((Fraction(1, p**(a+1)) for p, a in fac.items() if p*p <= m), Fraction())
        high = loss-low
        k = isqrt(m)
        assert low <= Fraction(k, m)
        assert high <= Fraction(1, k)
        assert 1-loss <= delta(m) <= 1
        if m in (2, 3, 5, 10, 20, 40, 80, 120):
            rows.append({'m': m, 'delta': wire(delta(m)), 'local_loss_sum': wire(loss),
                         'rational_loss_upper': wire(Fraction(k, m)+Fraction(1, k))})
    return {'m_range': [2, 120], 'rows': rows}


def zero_fiber_checks():
    rows = []
    for m in (3, 4, 5, 8, 12, 20, 32):
        b, fac = factorial(m), factorial_factors(m)
        for width in (2, 3, 5):
            support = [p for p in primes_through(width*m) if p > m]
            p_value = prod(support)
            a = b*p_value
            assert gcd(b, p_value) == 1 and a % b == b % b == 0
            assert 1 <= b <= a <= b**8
            combined = dict(fac)
            combined.update({p: 1 for p in support})
            za, zb = z_from_factors(combined), z_from_factors(fac)
            zp = prod((Fraction(p+1, p) for p in support), start=Fraction(1))
            assert za/zb == zp and za-zb == zb*(zp-1)
            # The logarithmic expansion's total quadratic error is bounded by this sum.
            square_tail = sum((Fraction(1, p*p) for p in support), Fraction())
            assert square_tail < Fraction(1, m)
            rows.append({'m': m, 'prime_interval': [m+1, width*m], 'primes': support,
                         'height_power_C': 8, 'a': str(a), 'b': str(b),
                         'exact_weight_ratio': wire(zp), 'exact_weight_difference': wire(za-zb),
                         'reciprocal_square_sum': wire(square_tail)})
    return {'actual_same_zero_fiber_witnesses': len(rows), 'rows': rows}


def fib_table(n):
    values = [0, 1, 1]
    while values[-1] <= n:
        values.append(values[-1]+values[-2])
    return values


def canonical(n):
    values = fib_table(n)
    indices, remainder = [], n
    for i in range(len(values)-1, 1, -1):
        if values[i] <= remainder:
            indices.append(i)
            remainder -= values[i]
    indices.reverse()
    assert remainder == 0 and all(b-a >= 2 for a, b in zip(indices, indices[1:]))
    return indices, values


def canonical_composition(n):
    indices, values = canonical(n)
    x = (0, 0)
    for i in indices:
        if i >= 3:
            d = i-3
            x = (x[0]+(1 if d == 0 else values[d-1]), x[1]+values[d])
    return indices, x


def canonical_flip_checks():
    flips = offsets = 0
    examples = []
    for m in range(1, 49):
        g = factorial(m)
        values = fib_table(g*g*10)
        j = 2
        # For even j, phi^j=L_j-phi^-j is strictly between L_j-1 and L_j.
        while values[j-1]+values[j+1] <= g:
            j += 2
        r = j+6*m+3
        while len(values) <= r:
            values.append(values[-1]+values[-2])
        center = g*values[r]
        indices, x = canonical_composition(center)
        next_indices, next_x = canonical_composition(center+1)
        assert indices[0] >= 6*m+3
        assert 2 not in indices and next_indices == [2]+indices
        assert next_x == x == (g*values[r-4], g*values[r-3])
        assert gcd(*x) == g and x[0]**2+x[0]*x[1]-x[1]**2 == g*g
        assert 2*x[0]+3*x[1] == center and gcd(center+1, g) == 1
        flips += 1
        primes = primes_through(m)
        for h in (-m*m, -m, -1, 1, m, m*m):
            assert center+h > 0
            assert gcd(center+h, g) == gcd(abs(h), g)
            ratio = Fraction(1)
            for p in primes:
                ratio *= local_z(p, valuation(center+h, p))/local_z(p, valuation(h, p))
            assert delta(m) <= ratio <= 1/delta(m)
            offsets += 1
        if m in (1, 2, 3, 5, 10, 48):
            examples.append({'m': m, 'j': j, 'null_prefix_windows': 2*m,
                             'center': str(center), 'unit_one_quantity': str(center+1),
                             'same_composition': [str(a) for a in x],
                             'center_indices': indices, 'unit_one_indices': next_indices})
    return {'m_range': [1, 48], 'same_word_unit_flips': flips,
            'signed_offset_local_factor_checks': offsets, 'examples': examples}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path, help='output JSON file')
    args = parser.parse_args()
    if not __debug__:
        parser.error('assertions must be enabled; do not use -O or PYTHONOPTIMIZE')
    source = Path(__file__).resolve()
    if args.out.resolve() == source or (args.out.exists() and args.out.samefile(source)):
        parser.error('--out must not overwrite the program source')
    report = {'schema': 'modular-resolution-finite-v1', 'source': source.name,
              'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'scope': 'Finite exact local arithmetic and actual canonical sources; no infinite or Lean certification.',
              'local_congruence': local_checks(), 'factorial_truncation': truncation_checks(),
              'sharpness_zero_fiber': zero_fiber_checks(), 'canonical_unit_flip': canonical_flip_checks()}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print(json.dumps({'same_residue_pairs': report['local_congruence']['same_residue_pairs'],
                      'opposite_residue_pairs': report['local_congruence']['opposite_residue_pairs'],
                      'zero_fiber_witnesses': report['sharpness_zero_fiber']['actual_same_zero_fiber_witnesses'],
                      'unit_flips': report['canonical_unit_flip']['same_word_unit_flips'],
                      'offset_checks': report['canonical_unit_flip']['signed_offset_local_factor_checks'],
                      'source_sha256': report['source_sha256']}, sort_keys=True))


if __name__ == '__main__':
    main()
