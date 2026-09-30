#!/usr/bin/env python3
"""Finite exact diagnostics for canonical sources with arbitrary content.

Python 3.9+, standard library only; runnable from any working directory.
Every selected source is reconstructed from its canonical Zeckendorf address.
These checks do not prove the infinite asymptotics, Robin, RH or a Lean theorem.
"""

import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from math import factorial, gcd, isqrt, prod
from pathlib import Path


WINDOWS = {0: ('null', (0, 0)), 1: ('2', (1, 0)),
           2: ('3', (0, 1)), 4: ('5', (1, 1)), 5: ('25', (2, 1))}


def sign(x):
    """Exact sign of a+b*phi: compare u+v*sqrt(5), never floats."""
    u, v = 2*x[0]+x[1], x[1]
    if v == 0:
        return (u > 0)-(u < 0)
    if u >= 0 and v > 0:
        return 1
    if u <= 0 and v < 0:
        return -1
    difference = u*u-5*v*v if u > 0 else 5*v*v-u*u
    assert difference != 0
    return 1 if difference > 0 else -1


def mul(x, y):
    a, b = x
    c, d = y
    return a*c+b*d, a*d+b*c+b*d


def conjugate(x):
    return x[0]+x[1], -x[1]


def norm(x):
    a, b = x
    return a*a+a*b-b*b


def phi_power(n):
    assert n >= 0
    x, base = (1, 0), (0, 1)
    while n:
        if n & 1:
            x = mul(x, base)
        base = mul(base, base)
        n //= 2
    return x


@lru_cache(maxsize=None)
def fib_pair(n):
    """Fast doubling, independent of the greedy address's Fibonacci table."""
    if n == 0:
        return 0, 1
    a, b = fib_pair(n//2)
    c, d = a*(2*b-a), a*a+b*b
    return (d, c+d) if n % 2 else (c, d)


def fib(n):
    return fib_pair(n)[0]


def select_even(g):
    assert g >= 1
    j, value = 2, (1, 1)
    while sign((value[0]-g, value[1])) <= 0:
        j += 2
        value = mul(value, (1, 1))
    assert value == (fib(j-1), fib(j))
    previous = phi_power(j-2)
    assert sign((previous[0]-g, previous[1])) <= 0
    # For positive even j, phi^j=L_j-phi^-j lies strictly in (L_j-1,L_j).
    assert g < fib(j-1)+fib(j+1)
    if j > 2:
        assert g >= fib(j-3)+fib(j-1)
    return j


def canonical(n):
    assert n >= 1
    values = [0, 1, 1]
    while values[-1] <= n:
        values.append(values[-1]+values[-2])
    remainder, indices = n, []
    for i in range(len(values)-1, 1, -1):
        if values[i] <= remainder:
            indices.append(i)
            remainder -= values[i]
    indices.reverse()
    assert remainder == 0 and sum(values[i] for i in indices) == n
    assert all(b-a >= 2 for a, b in zip(indices, indices[1:]))
    return indices


def decode(indices):
    unit = int(2 in indices)
    powers = [i-3 for i in indices if i >= 3]
    x = (0, 0)
    for d in powers:
        value = phi_power(d)
        x = x[0]+value[0], x[1]+value[1]
    if not powers:
        return unit, x, []
    occupied = set(powers)
    masks = [sum(1 << b for b in range(3) if 3*w+b in occupied)
             for w in range(max(powers)//3+1)]
    assert masks[-1] != 0  # End follows a nonzero window, not necessarily bit 1.
    seam = unit
    for mask in masks:
        assert mask in WINDOWS and not (seam and mask & 1)
        seam = (mask >> 2) & 1
    by_windows = (0, 0)
    for mask in reversed(masks):
        by_windows = mul((1, 2), by_windows)  # phi^3
        digit = WINDOWS[mask][1]
        by_windows = by_windows[0]+digit[0], by_windows[1]+digit[1]
    assert by_windows == x
    return unit, x, masks


def check_source(g, null_windows=0):
    assert null_windows >= 0 and null_windows % 2 == 0
    j = select_even(g)
    shifted_j = j+3*null_windows
    n = g*fib(shifted_j+3)
    indices = canonical(n)
    unit, x, masks = decode(indices)
    expected = (g*fib(shifted_j-1), g*fib(shifted_j))
    assert unit == 0 and x == expected and n == 2*x[0]+3*x[1]
    assert gcd(*x) == g and norm((x[0]//g, x[1]//g)) == 1
    y = conjugate(x)
    assert sign(y) > 0 and sign((1-y[0], -y[1])) > 0
    assert mul(y, phi_power(shifted_j)) == (g, 0)
    assert masks[:null_windows] == [0]*null_windows
    if null_windows == 0:
        assert g*g < n <= 5*g*g < 6*g*g
    return {'g': str(g), 'j': j, 'low_null_windows_inserted': null_windows,
            'N': str(n), 'composition': [str(a) for a in x], 'unit_bit': unit,
            'primitive_norm': 1, 'fundamental_discriminant_absolute': 4,
            'window_count': len(masks), 'indices': indices,
            'low_to_high_windows': [WINDOWS[mask][0] for mask in masks]+['End']}


def primes_through(limit):
    sieve = bytearray(b'\x01')*(limit+1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit)+1):
        if sieve[p]:
            sieve[p*p:limit+1:p] = b'\x00'*((limit-p*p)//p+1)
    return [p for p in range(2, limit+1) if sieve[p]]


@lru_cache(maxsize=None)
def factors(n):
    assert n >= 1
    original, out, p = n, [], 2
    while p*p <= n:
        exponent = 0
        while n % p == 0:
            exponent += 1
            n //= p
        if exponent:
            out.append((p, exponent))
        p = 3 if p == 2 else p+2
    if n > 1:
        out.append((n, 1))
    assert prod(p**e for p, e in out) == original
    assert all(all(p % d for d in range(2, isqrt(p)+1)) for p, _ in out)
    return tuple(out)


def first_rank(p, index):
    a, b = 0, 1
    for d in range(1, index+1):
        a, b = b, (a+b) % p
        if a == 0:
            assert index % d == 0
            return d
    raise AssertionError('actual prime divisor has no rank through its index')


def rational(value):
    return [value.numerator, value.denominator]


@lru_cache(maxsize=None)
def log_interval(n):
    """Outward dyadic interval for log(integer n), from the atanh series."""
    assert n >= 1

    def series(z):
        term, total = z, Fraction()
        for i in range(40):
            total += 2*term/(2*i+1)
            term *= z*z
        remainder = 2*term/(81*(1-z*z))
        return total, total+remainder

    exponent = n.bit_length()-1
    scale = 1 << exponent
    z = Fraction(n-scale, n+scale)
    low, high = series(z)
    low_two, high_two = series(Fraction(1, 3))
    low += exponent*low_two
    high += exponent*high_two
    wire = 1 << 80
    return (Fraction((low*wire).__floor__(), wire),
            Fraction((high*wire).__ceil__(), wire))


def ceiling_five_sixths(r):
    low, high = 0, r+1
    while high-low > 1:
        mid = (low+high)//2
        if mid**6 < r**5:
            low = mid
        else:
            high = mid
    assert (high-1)**6 < r**5 <= high**6
    return high


def check_rank_tail(r, y):
    """Finite stronger rational check of both logarithmic rank-bucket bounds."""
    assert r >= 6 and y >= 5
    buckets = defaultdict(list)
    for p, _ in factors(fib(r)):
        if p > y:
            buckets[first_rank(p, r)].append(p)
    checked = []
    for d, primes in sorted(buckets.items()):
        assert d > 5 and r % d == 0
        assert fib(d) % prod(primes) == 0 and y**len(primes) < prod(primes)
        # log(p/(p-1)) < 1/(p-1); bound this exact larger mass.
        mass = sum((Fraction(1, p-1) for p in primes), Fraction())
        log_y_high = log_interval(y)[1]
        log_d_low = log_interval(d)[0]
        first_bound_low = Fraction(d, y)/log_y_high
        second_bound_low = 6*(1+log_d_low)/d
        assert mass <= first_bound_low and mass <= second_bound_low
        checked.append({'rank': d, 'primes': primes,
                        'reciprocal_mass_upper_for_log_sum': rational(mass)})
    return {'r': r, 'y': y, 'nonempty_buckets': checked}


def rank_checks(max_m):
    rows, prime_checks = [], 0
    for m in range(2, max_m+1):
        g = factorial(m)
        r = select_even(g)+3
        factor_list = factors(fib(r))
        buckets = defaultdict(list)
        for p, _ in factor_list:
            rank = first_rank(p, r)
            prime_checks += 1
            if p not in (2, 5):
                chi = pow(5, (p-1)//2, p)
                assert chi in (1, p-1)
                assert (p-(1 if chi == 1 else -1)) % rank == 0
            if p > m:
                buckets[rank].append(p)
        details = []
        for d, primes in sorted(buckets.items()):
            assert fib(d) % prod(primes) == 0
            assert m**len(primes) < prod(primes) <= fib(d)
            mass = sum((Fraction(1, p-1) for p in primes), Fraction())
            assert mass <= Fraction(len(primes), m)
            details.append({'rank': d, 'primes': primes,
                            'sum_reciprocal_p_minus_one': rational(mass)})
        factorial_factors = dict(factors(g))
        n_factors = Counter(factorial_factors)
        n_factors.update(dict(factor_list))
        assert prod(p**a for p, a in n_factors.items()) == g*fib(r)
        z_g = prod((Fraction(p**(a+1)-1, p**a*(p-1))
                    for p, a in factorial_factors.items()), start=Fraction(1))
        z_n = prod((Fraction(p**(a+1)-1, p**a*(p-1))
                    for p, a in n_factors.items()), start=Fraction(1))
        totient_ratio = prod((Fraction(p, p-1) for p in n_factors),
                            start=Fraction(1))
        assert z_g <= z_n < totient_ratio
        y = ceiling_five_sixths(r)
        small_fibonacci_support = prod(p for p, _ in factor_list if p <= y)
        b_value = g*small_fibonacci_support
        assert g*fib(r) % b_value == 0
        b_primes = set(factorial_factors) | {p for p, _ in factor_list if p <= y}
        b_ratio = prod((Fraction(p, p-1) for p in b_primes), start=Fraction(1))
        large_fib_ratio = prod((Fraction(p, p-1) for p, _ in factor_list if p > y),
                              start=Fraction(1))
        assert totient_ratio <= b_ratio*large_fib_ratio
        rows.append({'m': m, 'fibonacci_index': r,
                     'complete_fibonacci_factorization': factor_list,
                     'large_prime_rank_buckets': details,
                     'Z_factorial': rational(z_g), 'Z_N': rational(z_n),
                     'N_over_totient': rational(totient_ratio),
                     'support_split_y': y, 'small_support_augmented_B': str(b_value),
                     'B_over_totient': rational(b_ratio),
                     'large_fibonacci_euler_product': rational(large_fib_ratio)})
    tail_rows = [check_rank_tail(r, y) for r in range(7, 64, 2)
                 for y in sorted({5, 7, 11, ceiling_five_sixths(r)})]
    return {'factorial_m_range': [2, max_m], 'actual_prime_rank_checks': prime_checks,
            'scope': 'Finite rank packing and exact Euler factors; no infinite tail claim.',
            'rows': rows, 'tail_bound_rows': tail_rows,
            'tail_nonempty_bucket_checks': sum(len(row['nonempty_buckets']) for row in tail_rows),
            'tail_bound': 'sum log(p/(p-1)) <= min(d/(y log y), 6(1+log d)/d)',
            'tail_bound_verification': 'Exact reciprocal upper mass compared with outward log intervals.'}


def strip_checks():
    checked = accepted = 0
    for a in range(-40, 81):
        for b in range(-40, 81):
            n = 2*a+3*b
            if n <= 0:
                continue
            checked += 1
            y = conjugate((a, b))
            if sign((y[0]+1, y[1])) > 0 and sign((-y[0], 1-y[1])) > 0:
                unit, actual, _ = decode(canonical(n))
                assert unit == 0 and actual == (a, b)
                accepted += 1
    return {'integer_composition_box': [-40, 80], 'positive_quantity_points': checked,
            'strict_strip_points_reconstructed': accepted}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path, help='output JSON file')
    args = parser.parse_args()
    if not __debug__:
        parser.error('assertions must be enabled; do not use -O or PYTHONOPTIMIZE')
    source = Path(__file__).resolve()
    if args.out.resolve() == source:
        parser.error('--out must not overwrite the program source')
    digest = hashlib.sha256()
    counts = Counter()
    samples = {}
    for g in range(1, 10001):
        row = check_source(g)
        digest.update(json.dumps(row, sort_keys=True).encode())
        counts['consecutive_contents'] += 1
        if g in (1, 2, 3, 5, 6, 10, 30, 210):
            samples[str(g)] = row
    for m in range(2, 121):
        row = check_source(factorial(m))
        digest.update(json.dumps(row, sort_keys=True).encode())
        counts['factorials'] += 1
    primorial = 1
    for p in primes_through(101):
        primorial *= p
        row = check_source(primorial)
        digest.update(json.dumps(row, sort_keys=True).encode())
        counts['primorials'] += 1
    for g in (1, 2, 30, 210, factorial(20), factorial(120), primorial):
        original = check_source(g)
        for ell in (2, 4, 10, 20):
            row = check_source(g, ell)
            assert row['low_to_high_windows'] == (
                ['null']*ell+original['low_to_high_windows'])
            digest.update(json.dumps(row, sort_keys=True).encode())
            counts['even_null_prefixes'] += 1
    report = {
        'schema': 'canonical-content-finite-v1',
        'source': source.name,
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope': 'Finite exact canonical-source checks; no Lean or infinite Robin certification.',
        'selection': 'j is the least positive even integer with phi^j > g',
        'counts': dict(counts),
        'ranges': {'g': [1, 10000], 'factorial_m': [2, 120],
                   'primorial_largest_prime': 101, 'inserted_even_null_windows': [2, 4, 10, 20]},
        'all_source_rows_sha256': digest.hexdigest(),
        'source_examples': samples,
        'strip_converse': strip_checks(),
        'finite_rank_and_euler': rank_checks(14),
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print(json.dumps({'counts': dict(counts), 'strip_converse': report['strip_converse'],
                      'actual_prime_rank_checks': report['finite_rank_and_euler']['actual_prime_rank_checks'],
                      'tail_nonempty_bucket_checks': report['finite_rank_and_euler']['tail_nonempty_bucket_checks'],
                      'source_sha256': report['source_sha256']}, sort_keys=True))


if __name__ == '__main__':
    main()
