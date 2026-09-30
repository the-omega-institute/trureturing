#!/usr/bin/env python3
"""Exact finite prime-section diagnostics for FIB theory sections 196–199.

Only Python's standard library is used. This checks finite identities and root
permutations, not irreducibility, number-field degrees, Chebotarev or Robin.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from math import gcd
from pathlib import Path
import sys


def mul(v, w):
    a, b = v
    c, d = w
    return a * c + b * d, a * d + b * c + b * d


def power(v, exponent):
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = mul(result, v)
        v = mul(v, v)
        exponent //= 2
    return result


def trace(v):
    return 2 * v[0] + v[1]


def poly_add(a, b):
    size = max(len(a), len(b))
    result = [(a[i] if i < len(a) else 0) +
              (b[i] if i < len(b) else 0) for i in range(size)]
    while len(result) > 1 and result[-1] == 0:
        result.pop()
    return result


def poly_mul(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] += x * y
    return result


def poly_eval(a, x):
    value = 0
    for coefficient in reversed(a):
        value = value * x + coefficient
    return value


def primes_below(bound):
    sieve = bytearray(b'\x01') * bound
    sieve[:2] = b'\x00\x00'
    for p in range(2, bound):
        if sieve[p]:
            yield p
            for multiple in range(p * p, bound, p):
                sieve[multiple] = 0


def check_sources():
    polynomials = [[2], [0, 1]]
    for _ in range(2, 33):
        polynomials.append(poly_add([0] + polynomials[-1],
                                    [-x for x in polynomials[-2]]))
    primes = list(primes_below(500))
    seed, tau, phi = (16, 29), (-1, -1), (0, 1)
    counts = {'polynomial_identities': 0, 'integer_factorizations': 0,
              'actual_prime_congruences': 0, 'actual_factor_bridges': 0}
    witness_digest = hashlib.sha256()
    for k in (4, 8, 16, 24, 32):
        for r in range(0, k, 2):
            a_r = trace(mul(mul(seed, seed), power(tau, r + 3)))
            numerator = trace(mul(power((-2, 1), (r + 4) // 2), (29, -16)))
            assert a_r == 242 - numerator ** 2
            whole = poly_add([-121 * x for x in polynomials[k]], [-a_r])
            first = poly_add([11 * x for x in polynomials[k // 2]], [-numerator])
            second = poly_add([11 * x for x in polynomials[k // 2]], [numerator])
            assert poly_add(whole, poly_mul(first, second)) == [0]
            counts['polynomial_identities'] += 1
            for ell in range(10):
                j = r + k * ell
                composition = mul(power(phi, j), seed)
                value = 2 * composition[0] + 3 * composition[1]
                z = mul(power(phi, j // 2 + 2), (3, 2))
                u1, u2 = z[1], trace(z)
                assert u1 * u2 == value
                assert gcd(u1, u2) in (1, 2)
                assert u2 * u2 - 5 * u1 * u1 == 44 * (-1) ** (j // 2)
                counts['integer_factorizations'] += 1
                actual_root = trace(power(tau, ell))
                for p in primes:
                    if 110 % p == 0:
                        continue
                    if u1 % p == 0:
                        assert poly_eval(first, actual_root) % p == 0
                        counts['actual_factor_bridges'] += 1
                    if u2 % p == 0:
                        assert poly_eval(second, actual_root) % p == 0
                        counts['actual_factor_bridges'] += 1
                    if value % p == 0:
                        assert poly_eval(whole, actual_root) % p == 0
                        counts['actual_prime_congruences'] += 1
                        witness_digest.update(f'{k},{r},{ell},{p}\n'.encode())
    return {**counts, 'prime_incidence_sha256': witness_digest.hexdigest()}


def check_groups():
    rows = []
    for k in (4, 8, 16, 24, 32, 64, 128):
        elements = [(c, d) for c in range(k) if gcd(c, k) == 1
                    for d in range(0, k, 2)]
        counts = [0, 0, 0, 0]
        kernels = [[], []]
        for c, d in elements:
            fixed = [h for h in range(k) if (c * h + d - h) % k == 0]
            f0 = any(h % 2 == 0 for h in fixed)
            f1 = any(h % 2 == 1 for h in fixed)
            assert bool(fixed) == (d % gcd(c - 1, k) == 0)
            for i, event in enumerate((f0, f1, f0 and f1, f0 or f1)):
                counts[i] += event
            for parity in (0, 1):
                if sum(h % 2 == parity for h in fixed) == k // 2:
                    kernels[parity].append([c, d])
            if k == 24:
                fixed8 = any((c * h + d - h) % 8 == 0 for h in range(8))
                fixed3 = any((c * h + d - h) % 3 == 0 for h in range(3))
                assert bool(fixed) == (fixed8 and fixed3)
        size = len(elements)
        if k == 24:
            assert size == 96 and counts == [24, 24, 4, 44]
            assert len({(c % 8, d % 8, c % 3, d % 3) for c, d in elements}) == 96
            expected = Fraction(11, 24)
        else:
            n = k // 2
            assert size == n * n
            assert Fraction(counts[0], size) == Fraction(1, 3) + Fraction(2, 3 * n * n)
            assert counts[0] == counts[1] and counts[2] == 1
            assert kernels == [[[1, 0], [1 + n, 0]], [[1, 0], [1 + n, n]]]
            expected = Fraction(2, 3) + Fraction(4, 3 * k * k)
        assert Fraction(counts[3], size) == expected
        rows.append({'window': k, 'group_order': size,
                     'even_root_count': counts[0], 'odd_root_count': counts[1],
                     'both_count': counts[2], 'union_count': counts[3],
                     'union_fraction': str(expected), 'pointwise_kernels': kernels})
    return rows



def check_general_seeds():
    primes = list(primes_below(100))
    cases = incidences = 0
    phi, tau = (0, 1), (-1, -1)
    polynomials = [[2], [0, 1]]
    for _ in range(2, 22):
        polynomials.append(poly_add([0] + polynomials[-1],
                                    [-x for x in polynomials[-2]]))
    seeds = [(a, b) for a in range(7) for b in range(7) if gcd(a, b) == 1]
    for a, b in seeds:
        norm = a * a + a * b - b * b
        for k in (3, 7, 21):
            for r in range(k):
                target = trace(mul(mul((a, b), (a, b)), power(tau, r + 3)))
                for ell in range(5):
                    j = r + k * ell
                    pair = mul(power(phi, j), (a, b))
                    value = 2 * pair[0] + 3 * pair[1]
                    root = trace(power(tau, ell))
                    residue = norm * poly_eval(polynomials[k], root) - target
                    cases += 1
                    for prime in primes:
                        if (10 * norm) % prime and value % prime == 0:
                            assert residue % prime == 0
                            incidences += 1
    group_rows = []
    for k in (3, 7, 21, 39, 273):
        fixed_count = order = 0
        for c in range(k):
            if gcd(c, k) != 1:
                continue
            for d in range(k):
                has_root = any((c * h + d - h) % k == 0 for h in range(k))
                assert has_root == (d % gcd(c - 1, k) == 0)
                fixed_count += has_root
                order += 1
        totient = sum(gcd(c, k) == 1 for c in range(k))
        assert Fraction(fixed_count, order) == Fraction(totient, k)
        group_rows.append({'window': k, 'group_order': order,
                           'fixed_root_count': fixed_count,
                           'fixed_root_fraction': str(Fraction(fixed_count, order))})
    return {'coefficient_range': '0 <= a,b <= 6; gcd(a,b)=1',
            'seeds': len(seeds), 'windows': [3, 7, 21],
            'quotients': '0 <= ell < 5', 'prime_cutoff_exclusive': 100,
            'integer_cases': cases, 'actual_prime_congruences': incidences,
            'odd_squarefree_root_groups': group_rows}



def check_missing_prime():
    p = 113
    reduce_pair = lambda value: tuple(x % p for x in value)
    tau, theta = (-1, -1), (54, 91)
    powers = {'tau2': reduce_pair(power(tau, 2)),
              'tau16': reduce_pair(power(tau, 16)),
              'tau19': reduce_pair(power(tau, 19)),
              'theta2': reduce_pair(power(theta, 2)),
              'theta4': reduce_pair(power(theta, 4)),
              'theta32': reduce_pair(power(theta, 32)),
              'theta38': reduce_pair(power(theta, 38))}
    assert powers == {'tau2': (2, 3), 'tau16': (100, 8), 'tau19': (1, 0),
                      'theta2': (10, 29), 'theta4': (37, 65),
                      'theta32': (70, 54), 'theta38': (9, 94)}
    assert [pow(5, e, p) for e in (8, 16, 32, 56)] == [97, 30, 109, 112]
    polynomials = [[2], [0, 1]]
    for _ in range(2, 25):
        polynomials.append(poly_add([0] + polynomials[-1],
                                    [-x for x in polynomials[-2]]))
    for r in range(0, 24, 2):
        target = trace(mul(mul((16, 29), (16, 29)), power(tau, r + 3)))
        assert all((-121 * poly_eval(polynomials[24], x) - target) % p
                   for x in range(p))
    return {'prime': p, 'pair_powers': powers,
            'residue_polynomials_with_no_root': 12,
            'candidate_roots_checked': 12 * p}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        parser.error('optimized execution disables exact checks')
    source = Path(__file__).resolve()
    if args.out.resolve() == source or (args.out.exists() and args.out.samefile(source)):
        parser.error('output must not overwrite this program')
    result = {
        'scope': 'finite integer/polynomial identities and permutation counts; no analytic or Lean proof',
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'seed': [16, 29], 'source_windows': [4, 8, 16, 24, 32],
        'even_residues': 'all 0 <= r < k', 'quotients': '0 <= ell < 10',
        'prime_cutoff_exclusive': 500,
        'source_checks': check_sources(), 'root_groups': check_groups(),
        'general_seed_checks': check_general_seeds(),
        'missing_prime': check_missing_prime(),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'source_checks': result['source_checks'],
                      'group_windows': [row['window'] for row in result['root_groups']],
                      'general_seed_checks': result['general_seed_checks']}))


if __name__ == '__main__':
    main()
