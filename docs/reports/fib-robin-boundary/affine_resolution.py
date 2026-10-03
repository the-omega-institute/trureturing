#!/usr/bin/env python3
"""Exact diagnostics for finite FIB blocks, progressions and phase relations.

Python 3.9+, standard library only. This program checks finite arithmetic
bridges and constants; it does not certify the infinite Robin estimates.
"""

import argparse
from functools import lru_cache
from fractions import Fraction
import hashlib
import json
from math import factorial, gcd, prod
from pathlib import Path
import sys


A0 = Fraction(94243, 10**7)
DIGITS = {0: (0, 0), 1: (1, 0), 2: (0, 1),
          5: (2, 1), 4: (1, 1)}


def add(x, y):
    return x[0]+y[0], x[1]+y[1]


def neg(x):
    return -x[0], -x[1]


def mul(x, y):
    a, b = x
    c, d = y
    return a*c+b*d, a*d+b*c+b*d


def conj(x):
    return x[0]+x[1], -x[1]


def norm(x):
    product = mul(x, conj(x))
    assert product[1] == 0
    return product[0]


def power(x, n, modulus=None):
    result = (1, 0)
    while n:
        if n & 1:
            result = mul(result, x)
        x = mul(x, x)
        if modulus is not None:
            result = tuple(t % modulus for t in result)
            x = tuple(t % modulus for t in x)
        n //= 2
    return result


def sign(x):
    """Exact sign of a+b*phi, using integer comparisons with sqrt(5)."""
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


def less(x, y):
    return sign(add(y, neg(x))) > 0


@lru_cache(maxsize=None)
def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a+b
    return a


def lucas(n):
    return 2 if n == 0 else fib(n-1)+fib(n+1)


def fib_mod(n, modulus):
    a, b = 0, 1
    for bit in bin(n)[2:]:
        c = a*(2*b-a) % modulus
        d = (a*a+b*b) % modulus
        a, b = (c, d) if bit == '0' else (d, (c+d) % modulus)
    return a


@lru_cache(maxsize=None)
def factors(n):
    n = abs(n)
    assert n > 0
    out, p = {}, 2
    while p*p <= n:
        if n % p == 0:
            out[p] = 0
            while n % p == 0:
                out[p] += 1
                n //= p
        p = 3 if p == 2 else p+2
    if n > 1:
        out[n] = 1
    return out


@lru_cache(maxsize=None)
def rank(p):
    if p == 2:
        return 3
    if p == 5:
        return 5
    legendre = pow(5, (p-1)//2, p)
    assert legendre in (1, p-1)
    z = p-(1 if legendre == 1 else -1)
    assert fib_mod(z, p) == 0
    for q in factors(z):
        while z % q == 0 and fib_mod(z//q, p) == 0:
            z //= q
    # Minimality among divisors of the classical rank bound.
    assert all(fib_mod(z//q, p) for q in factors(z))
    return z


def words(length):
    states = [(0, False)]
    for i in range(length):
        new = []
        for mask, previous in states:
            new.append((mask, False))
            if not previous:
                new.append((mask | (1 << i), True))
        states = new
    return [mask for mask, _ in states]


def window_checks():
    rows, shifts = [], 0
    for w in range(1, 7):
        n = 3*w
        phi_powers = [power((0, 1), i) for i in range(n+2)]
        count, peak, witness = 0, 0, None
        for mask in words(n):
            if mask == 0:
                continue
            x = (0, 0)
            for i in range(n):
                if mask & (1 << i):
                    x = add(x, phi_powers[i])
            by_windows = (0, 0)
            for j in reversed(range(w)):
                digit = DIGITS[(mask >> (3*j)) & 7]
                by_windows = add(mul((1, 2), by_windows), digit)
            assert x == by_windows
            assert less((0, 0), x) and less(x, phi_powers[n])
            assert less((-1, 0), conj(x)) and less(conj(x), (0, 1))
            b = abs(norm(x))
            assert b >= 1 and less((b, 0), phi_powers[n+1])
            assert 2*x[0]+3*x[1] == sum(
                fib(i+3) for i in range(n) if mask & (1 << i))
            for ell in range(9):
                shifted = mul(power((0, 1), 3*ell), x)
                assert abs(norm(shifted)) == b
                j = 3*ell+3
                assert 2*shifted[0]+3*shifted[1] == (
                    x[0]*fib(j)+x[1]*fib(j+1))
                shifts += 1
            count += 1
            if b > peak:
                peak, witness = b, mask
        rows.append({'windows': w, 'nonzero_words': count,
                     'maximum_abs_norm': peak, 'maximizing_mask': witness})
    return {'unit_bit': 0, 'null_windows_low_end': [0, 8],
            'rows': rows, 'shift_identities': shifts}


def norm_threshold_checks():
    cases = excluded = units = 0
    for a in range(41):
        for b in range(41):
            if a == b == 0:
                continue
            g = gcd(a, b)
            full = abs(norm((a, b)))
            delta = abs(norm((a//g, b//g)))
            assert full == g*g*delta and full > 0
            h = 56
            while (h-2)**3 < 5040*A0*max(full, 7):
                h += 1
            if delta > 1:
                for p in factors(delta):
                    exponent = factors(5040*g).get(p, 0)
                    assert p <= delta and p**(exponent+1) <= 5040*full
                    if exponent:
                        assert h**3 > A0*(p**(exponent+1)-1)
                    else:
                        assert h**3 > 2*A0*(p-1)
                        # log(p) <= p-1: a stronger finite rational check.
                        assert Fraction(19, 7)**h > 2*(p-1)**2
                    excluded += 1
            else:
                assert (a//g, b//g) in [(1, 0), (0, 1)] + [
                    (fib(r-1), fib(r)) for r in range(2, 20)]
                for p, exponent in factors(5040*g).items():
                    assert p**(exponent+1) <= (5040*full if g % p == 0 else 49)
                    assert (h-2)**3 >= A0*(p**(exponent+1)-1)
                units += 1
            cases += 1
    assert 5040*A0 > 1 and 56**2 > 2160
    assert 5040*A0*Fraction(13, 8) < 125
    assert Fraction(13, 8)**2 > Fraction(13, 8)+1
    assert 54**3 > 5040*A0*7
    return {'coefficient_range': [0, 40], 'nonzero_seeds': cases,
            'primitive_norm_prime_checks': excluded, 'unit_seeds': units,
            'analytic_scope': 'finite hypotheses and constants, not Robin verification'}


def progression_checks():
    cases = prime_checks = 0
    branches = {'even_d': 0, 'odd_d_odd_h': 0, 'odd_d_even_h': 0}
    for a in range(3, 31):
        for d in range(1, 13):
            for h in range(1, 31):
                m, r = a+(h-1)*d, a+2*d*(h-1)
                v = sum(fib(a+2*d*j) for j in range(h))
                if d % 2 == 0:
                    key, den, left, right = 'even_d', fib(d), fib(m), fib(h*d)
                    ranks = (m, h*d)
                elif h % 2:
                    key, den, left, right = 'odd_d_odd_h', lucas(d), fib(m), lucas(h*d)
                    ranks = (m, 2*h*d)
                else:
                    key, den, left, right = 'odd_d_even_h', lucas(d), lucas(m), fib(h*d)
                    ranks = (2*m, h*d)
                assert den*v == left*right and right % den == 0
                assert v >= fib(r)
                if h >= 2:
                    assert m <= r and h*d <= r
                else:
                    ranks = (a,)
                if r <= 42:
                    for p in factors(v):
                        z = rank(p)
                        assert any(index % z == 0 for index in ranks)
                        prime_checks += 1
                branches[key] += 1
                cases += 1
    return {'a_range': [3, 30], 'd_range': [1, 12], 'h_range': [1, 30],
            'identities': cases, 'branches': branches,
            'complete_factorization_R_at_most': 42,
            'actual_prime_carrier_checks': prime_checks}


def odd_phase_checks():
    cases = prime_checks = 0
    for a in range(5, 101):
        for b in range(2, a-2):
            if (a-b) % 2 == 0:
                continue
            k, t, v = a-b, a+b, fib(a)+fib(b)
            assert fib(t)*fib(k) == fib(a)**2+fib(b)**2
            assert lucas(t)*lucas(k) == 5*v*(fib(a)-fib(b))+4*(-1)**a
            assert 4 % gcd(v, lucas(t)*lucas(k)) == 0
            pk = power((0, 1), k)
            left = add(mul(power((0, 1), t), add(pk, (1, 0))),
                       tuple(-(-1)**b*z for z in add(pk, (-1, 0))))
            right = tuple(v*z for z in mul((-1, 2), power((0, 1), a)))
            assert left == right and norm(add(pk, (1, 0))) == lucas(k)
            if a <= 36:
                for p in factors(v):
                    if p == 2:
                        continue
                    z = rank(p)
                    assert (2*t % z == 0 or 2*k % z == 0) == (gcd(a, b) % z == 0)
                    if p != 5:
                        assert gcd(lucas(k), p) == 1
                        den = add(pk, (1, 0))
                        inverse = tuple(pow(norm(den) % p, -1, p)*c for c in conj(den))
                        image = tuple((-1)**b*c % p for c in mul(add(pk, (-1, 0)), inverse))
                        assert image == power((0, 1), t, p)
                        tau = (-1, -1)
                        assert power(tau, z, p) == (1, 0)
                        assert all(power(tau, z//q, p) != (1, 0) for q in factors(z))
                        assert tuple(c % p for c in mul(add((1, 0), power(tau, k, p)),
                                                        add((1, 0), power(tau, t, p)))) == tuple(
                            4*c % p for c in power(tau, a, p))
                    prime_checks += 1
            cases += 1
    assert fib(11)+fib(6) == 97 and rank(97) == 49
    assert all(index % 7 for index in (11, 6, 17, 5))
    assert fib(8)-fib(3) == 19 and fib(8)+fib(3) == 23
    # A true rank relation on the difference branch, not the sum branch.
    p, tau = 19, (-1, -1)
    assert tuple(c % p for c in mul(add((1, 0), power(tau, 5, p)),
                                    add((1, 0), power(tau, 11, p)))) == tuple(
        4*c % p for c in power(tau, 8, p))
    return {'a_range': [5, 100], 'b_minimum': 2, 'odd_gap_minimum': 3,
            'joint_identities': cases, 'factorization_a_at_most': 36,
            'actual_prime_phase_checks': prime_checks,
            'doubling_carrier_obstruction': {'a': 11, 'b': 6, 'p': 97, 'rank': 49},
            'lost_sign_obstruction': {'a': 8, 'b': 3, 'p': 19, 'sum': 23}}


def complete_local_phases():
    counts = {'split': 0, 'nonsplit': 0, 'nonunit_denominator': 0,
              'sum_branch': 0, 'difference_only': 0}
    for p in range(3, 100, 2):
        if p == 5 or factors(p) != {p: 1}:
            continue
        kind = 'split' if pow(5, (p-1)//2, p) == 1 else 'nonsplit'
        for a in range(5, 41):
            for b in range(2, a-2):
                if (a-b) % 2 == 0:
                    continue
                k, t, v = a-b, a+b, fib(a)+fib(b)
                pk = power((0, 1), k, p)
                den = add(pk, (1, 0))
                unit = norm(den) % p != 0
                equation = False
                if unit:
                    inverse = tuple(pow(norm(den) % p, -1, p)*c for c in conj(den))
                    value = tuple((-1)**b*c % p for c in mul(add(pk, (-1, 0)), inverse))
                    equation = value == power((0, 1), t, p)
                else:
                    counts['nonunit_denominator'] += 1
                assert (v % p == 0) == (unit and equation)
                tau = (-1, -1)
                left = mul(add((1, 0), power(tau, k, p)),
                           add((1, 0), power(tau, t, p)))
                rank_equation = tuple(c % p for c in left) == tuple(
                    4*c % p for c in power(tau, a, p))
                assert rank_equation == (v*(fib(a)-fib(b)) % p == 0)
                counts[kind] += 1
                counts['sum_branch'] += v % p == 0
                counts['difference_only'] += rank_equation and v % p != 0
    return {'prime_range_excluding_2_5': [3, 99], 'a_range': [5, 40],
            'counts': counts}


def valuation(n, p):
    assert n > 0
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def two_factor_stops():
    primes = (2, 3, 5, 7, 11, 13, 17, 19, 23)
    stops = (20, 12, 8, 6, 5, 4, 4, 4, 3)
    losses = (2, 1, 0, 1, 1, 1, 1, 1, 1)
    lower_v = tuple(e+1-valuation(5040, p) for p, e in zip(primes, stops))
    forced = tuple(e-2*loss for e, loss in zip(lower_v, losses))
    assert lower_v == (17, 11, 8, 6, 6, 5, 5, 5, 4)
    assert forced == (13, 9, 8, 4, 4, 3, 3, 3, 2)
    first = []
    for p, z in zip((3, 7, 11, 13, 17, 19, 23), (4, 8, 10, 7, 9, 18, 24)):
        assert all(fib(j) % p for j in range(1, z))
        assert valuation(fib(z), p) == 1 and z % p != 0
        first.append({'p': p, 'rank': z, 'fib_at_rank': fib(z)})
    checks = 0
    for t in range(1, 2001):
        for value in (fib(t), lucas(t)):
            for p, loss in zip(primes, losses):
                assert valuation(value, p) <= valuation(t, p)+loss
                checks += 1
    force_product = prod(p**e for p, e in zip(primes, forced))
    assert force_product == 86715646730220994462337961600000000
    assert force_product*18**80 > 49**80
    # Outward bounds for e from its factorial series.
    e_lower = sum((Fraction(1, factorial(j)) for j in range(9)), Fraction(0))
    e_upper = e_lower+Fraction(1, factorial(9))*Fraction(10, 9)
    assert Fraction(65, 24) < e_lower < e_upper < Fraction(49, 18)
    k = 2**7*3**5*5**5*7**3*11**3
    r = 5*k-2
    observed = []
    for p, exponent in zip(primes, (23, 15, 11, 9, 8, 2, 2, 2, 2)):
        modulus = p**(exponent+1)
        f3, f2 = fib_mod(3*k, modulus), fib_mod(2*k, modulus)
        # Golden-ring binary powering is independent of fast doubling.
        assert f3 == power((0, 1), 3*k, modulus)[1]
        assert f2 == power((0, 1), 2*k, modulus)[1]
        residue = 5040*f3*f2 % modulus
        assert residue and valuation(residue, p) == exponent
        observed.append({'p': p, 'modulus': modulus, 'residue': residue,
                         'exact_n_valuation': exponent})
    eta = prod(1-Fraction(1, p**(e+1)) for p, e in zip(primes[:5], (23, 15, 11, 9, 8)))
    assert 1-eta == Fraction(2842521061260042618529, 31272425262685292301000000000)
    assert 1-eta < A0/(35**3+A0)
    assert 5*k < Fraction(65, 24)**35 and Fraction(r, 4) > 32*10**12
    assert 5040 < 2**13 and Fraction(3, 4)*(5*k+13) < 5*k
    assert sum((Fraction(3, 4)**j/factorial(j) for j in range(5)), Fraction(0)) > 2
    return {'published_stops_are_external_inputs': True,
            'primes': primes, 'safe_n_valuation_caps': stops,
            'forced_V_valuations': lower_v, 'forced_rs_valuations': forced,
            'first_rank_data': first, 't_range': [1, 2000],
            'uniform_F_and_L_valuation_checks': checks,
            'forced_index_product': force_product,
            'integer_comparison_slack': force_product*18**80-49**80,
            'five_direction_obstruction': {
                'K': k, 'a': k+2, 'd': 2, 'h': k, 'largest_occupied_index': r,
                'factor_indices': [3*k, 2*k], 'observations': observed,
                'eta_five': [eta.numerator, eta.denominator],
                'log_log_n_upper_bound': 35, 'passes_new_prime_17_stop': True}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='output JSON file (overwritten)')
    args = parser.parse_args()
    if not __debug__:
        parser.error('optimized Python disables verification; run without -O')
    result = {'scope': 'finite exact diagnostics; not a proof of Robin or RH',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'window_geometry': window_checks(),
              'norm_threshold': norm_threshold_checks(),
              'progressions': progression_checks(),
              'odd_phases': odd_phase_checks(),
              'complete_local_phases': complete_local_phases(),
              'two_factor_stops': two_factor_stops()}
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
