#!/usr/bin/env python3
"""Exact diagnostics for the five classical Robin stops on 5040*F_j.

Standard-library arithmetic only. This is not a proof of the cited valuation
theorems and does not authenticate a supplied integer's claimed source index.
F_0=0, F_1=1, F_(j+2)=F_(j+1)+F_j throughout.
"""
import sys
sys.dont_write_bytecode = True

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path
from random import Random

PRIMES = (2, 3, 5, 7, 11)
BASE = {2: 4, 3: 2, 5: 1, 7: 1, 11: 0}
STOP = {2: 20, 3: 12, 5: 8, 7: 6, 11: 5}
FAIL_MODULI = {2: 3 * 2**15, 3: 4 * 3**10, 5: 5**8,
               7: 8 * 7**5, 11: 10 * 11**5}
D = 2**15 * 3**10 * 5**8 * 7**5 * 11**5


def valuation(n, p):
    if type(n) is not int or n <= 0:
        raise ValueError('valuation requires a positive integer')
    result = 0
    while n % p == 0:
        n //= p
        result += 1
    return result


def predicted_fib_valuation(j, p):
    if type(j) is not int or j < 1:
        raise ValueError('positive standard Fibonacci index required')
    if p == 2:
        if j % 3:
            return 0
        return valuation(j, 2) + 2 if j % 2 == 0 else 1
    if p == 5:
        return valuation(j, 5)
    rank = {3: 4, 7: 8, 11: 10}[p]
    return valuation(j, p) + 1 if j % rank == 0 else 0


def index_stops(j):
    """Conditional on the standard Fibonacci source semantics, no huge F_j."""
    if type(j) is not int or j < 3:
        raise ValueError('j >= 3 is required for 5040*F_j > 5040')
    vals = {p: BASE[p] + predicted_fib_valuation(j, p) for p in PRIMES}
    return {'index': j, 'n_valuations': vals,
            'stopping_primes': [p for p in PRIMES if vals[p] <= STOP[p]],
            'all_five_fail': all(vals[p] > STOP[p] for p in PRIMES)}


def fib_mod_doubling(j, modulus):
    """Pair invariant: (F_k,F_(k+1)) modulo modulus for consumed binary k."""
    a, b = 0, 1
    for digit in bin(j)[2:]:
        c = a * (2*b - a) % modulus
        d = (a*a + b*b) % modulus
        a, b = (d, (c+d) % modulus) if digit == '1' else (c, d)
    return a


def fib_mod_matrix(j, modulus):
    """Independent binary powering of [[1,1],[1,0]], reading entry (0,1)."""
    def mul(a, b):
        return ((a[0]*b[0]+a[1]*b[2]) % modulus,
                (a[0]*b[1]+a[1]*b[3]) % modulus,
                (a[2]*b[0]+a[3]*b[2]) % modulus,
                (a[2]*b[1]+a[3]*b[3]) % modulus)
    result, power = (1, 0, 0, 1), (1, 1, 1, 0)
    while j:
        if j & 1:
            result = mul(result, power)
        power = mul(power, power)
        j >>= 1
    return result[1]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out',type=Path,required=True,help='output directory')
    ap.add_argument('--limit',type=int,default=10000,help='positive direct Fibonacci cutoff')
    ap.add_argument('--seed',type=int,default=20260929)
    ap.add_argument('--index',type=int,action='append',default=[],help='additional standard index j >= 3')
    args = ap.parse_args()
    if args.limit < 1 or any(j < 3 for j in args.index):
        ap.error('--limit must be positive and each --index must be >= 3')
    # Sequential recurrence evaluates actual integers, without valuation formulas.
    limit = args.limit
    a, b = 0, 1
    prefix_comparisons = 0
    rank_hits = {}
    for j in range(1, limit+1):
        a, b = b, a+b
        for p in PRIMES:
            actual = valuation(a, p)
            predicted = predicted_fib_valuation(j, p)
            assert actual == predicted, (j, p, actual, predicted)
            if actual and p not in rank_hits:
                rank_hits[p] = (j, actual)
            assert fib_mod_doubling(j, p**4) == a % (p**4)
            prefix_comparisons += 1
        if j >= 3:
            data = index_stops(j)
            assert data['all_five_fail'] == (j % D == 0)

    combined = 1
    for modulus in FAIL_MODULI.values():
        combined = combined * modulus // gcd(combined, modulus)
    assert combined == D

    indices = {D-2, D-1, D, D+1, D+2}
    indices.update(D//p for p in PRIMES)
    indices.update(D*p for p in PRIMES)
    for p, modulus in FAIL_MODULI.items():
        indices.update({modulus-1, modulus, modulus+1, modulus*p, modulus//p})
        rank = {2: 3, 3: 4, 5: 5, 7: 8, 11: 10}[p]
        indices.update(rank*p**e for e in range(1, 25))
    rng = Random(args.seed)
    for _ in range(32):
        indices.add(rng.randrange(3, 2**128))
        indices.add(D*rng.randrange(1, 2**48))

    indices.update(args.index)
    modular_checks = 0
    for j in sorted(indices):
        expected = index_stops(j)
        observed_stops = []
        for p in PRIMES:
            exponent = expected['n_valuations'][p]
            modulus = p**(exponent+1)
            f1 = fib_mod_doubling(j, modulus)
            f2 = fib_mod_matrix(j, modulus)
            assert f1 == f2, (j, p, 'recurrence implementations disagree')
            residue = 5040*f1 % modulus
            assert residue != 0 and valuation(residue, p) == exponent, (j, p)
            if valuation(residue, p) <= STOP[p]:
                observed_stops.append(p)
            assert (exponent > STOP[p]) == (j % FAIL_MODULI[p] == 0)
            modular_checks += 1
        assert observed_stops == expected['stopping_primes']
        assert (not observed_stops) == (j % D == 0)

    # Deliberate index shift: the boundary index and its successor disagree.
    p, modulus = 2, 2**22
    assert fib_mod_matrix(D, modulus) % 2**17 == 0
    assert fib_mod_matrix(D+1, modulus) % 2 == 1

    boundary_rows = [index_stops(D)] + [index_stops(D//p) for p in PRIMES]
    result = {'status': 'PASS', 'seed': args.seed, 'requested_indices': args.index, 'D': D, 'failure_moduli': FAIL_MODULI,
              'standard_source': 'F_0=0, F_1=1, F_(j+2)=F_(j+1)+F_j',
              'direct_integer_prefix': [1, limit],
              'direct_valuation_comparisons': prefix_comparisons,
              'first_prime_divisibility_indices_and_valuations': rank_hits,
              'large_modular_indices': len(indices),
              'large_modular_checks': modular_checks,
              'max_tested_index': max(indices),
              'index_shift_negative_control': 'F_D is divisible by 2^17; F_(D+1) is odd',
              'boundary_rows': boundary_rows,
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'limits': ['Finite diagnostics only; the infinite statement uses cited theorems.',
                         'No Lean compilation or kernel verification.',
                         'An arbitrary supplied integer needs a verified equality to 5040*F_j.']}
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'diagnostics.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
