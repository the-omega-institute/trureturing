#!/usr/bin/env python3
"""Exact finite prime-section diagnostics for FIB theory sections 196–205.

Only Python's standard library is used. This checks finite identities and root
permutations, not irreducibility, number-field degrees, Chebotarev or Robin.
"""
from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from itertools import product
from math import gcd, prod
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


def chi5(a):
    r = a % 5
    if r == 0:
        raise ValueError('chi5 requires a unit modulo 5')
    return 1 if r in (1, 4) else -1

def affine_experiment(k):
    primes = [p for p in primes_below(k + 1) if k % p == 0]
    assert k > 1 and k % 2 == 1 and k % 5 == 0
    assert prod(primes) == k, 'squarefree window required'
    units = [a for a in range(k) if gcd(a, k) == 1]
    twist = {a: chi5(a) * a % k for a in units}
    assert set(twist.values()) == set(units)
    assert all(twist[twist[a]] == a for a in units)
    assert chi5(-1) == 1
    assert all(twist[a*b % k] == twist[a]*twist[b] % k for a in units for b in units)
    permutations = set()
    coefficients = set()
    kernel = []
    counts = Counter()
    crt_coordinate_checks = 0
    for a in units:
        eps = chi5(a)
        for b in range(k):
            c, d = eps * a % k, eps * b % k
            permutation = tuple((eps * (a*h + b)) % k for h in range(k))
            assert len(set(permutation)) == k
            permutations.add(permutation)
            coefficients.add((c, d))
            fixed = sum(x == h for h, x in enumerate(permutation))
            counts[fixed] += 1
            if permutation == tuple(range(k)):
                kernel.append([a, b])
            for ell in primes:
                # Check every root-index coordinate in the same product action.
                assert all(permutation[h] % ell == (c*h+d) % ell for h in range(k))
                crt_coordinate_checks += k
    assert coefficients == set(product(units, range(k)))
    assert len(permutations) == len(units) * k
    local = {}
    crt_hist = Counter({1: 1})
    for ell in primes:
        hist = Counter()
        for c in range(1, ell):
            for d in range(ell):
                hist[sum((c*h+d) % ell == h for h in range(ell))] += 1
        assert hist == Counter({0: ell-1, 1: ell*(ell-2), ell: 1})
        local[str(ell)] = dict(sorted(hist.items()))
        new = Counter()
        for a, ca in crt_hist.items():
            for b, cb in hist.items():
                new[a*b] += ca*cb
        crt_hist = new
    assert counts == crt_hist
    total = k * len(units)
    with_fixed = total - counts[0]
    fraction = Fraction(with_fixed, total)
    expected = prod((Fraction(ell-1, ell) for ell in primes), start=Fraction(1))
    assert fraction == expected
    return {
        'k': k, 'prime_factors': primes, 'unit_count': len(units),
        'parameter_count': total, 'distinct_permutations': len(permutations),
        'twisted_slope_map_is_involution_and_bijection': True,
        'twisted_slope_map_is_group_automorphism': True,
        'chi5_minus_one': chi5(-1), 'kernel_parameters_A_b': kernel,
        'affine_coefficients_cover_full_AGL': True,
        'permutations_with_fixed_root': with_fixed,
        'fixed_root_fraction': str(fraction),
        'fixed_root_count_histogram': dict(sorted(counts.items())),
        'local_CRT_fixed_root_histograms': local,
        'CRT_histogram_matches_direct_enumeration': True,
        'CRT_coordinate_checks': crt_coordinate_checks,
    }

def qmul(v, w, p):
    return tuple(x % p for x in mul(v, w))

def qconj(v, p):
    x, y = v
    return ((x+y) % p, -y % p)

def qpow(v, n, p):
    assert n >= 0
    out = (1, 0)
    while n:
        if n & 1:
            out = qmul(out, v, p)
        v = qmul(v, v, p)
        n //= 2
    return out

def qinv(v, p):
    vc = qconj(v, p)
    norm, off = qmul(v, vc, p)
    assert off == 0 and norm != 0
    inv = pow(norm, -1, p)
    return (vc[0]*inv % p, vc[1]*inv % p)

def qtrace(v, p):
    return (2*v[0]+v[1]) % p

def dickson_and_derivative(n, x, p):
    if n == 0:
        return 2 % p, 0
    d0, d1, e0, e1 = 2 % p, x % p, 0, 1
    for _ in range(2, n+1):
        d0, d1, e0, e1 = d1, (x*d1-d0) % p, e1, (d1+x*e1-e0) % p
    return d1, e1

def divisor_bridge_experiment(k, seeds, max_index, prime_limit):
    primes = list(primes_below(prime_limit + 1))
    results = []
    for a, b in seeds:
        assert a >= 0 and b >= 0 and gcd(a,b) == 1
        norm = a*a+a*b-b*b
        assert norm != 0
        seq = [2*a+3*b, 3*a+5*b]
        while len(seq) <= max_index:
            seq.append(seq[-1]+seq[-2])
        eligible = [p for p in primes if (5*k*norm) % p != 0]
        tested = hits = trace_discriminant_zero = root_derivative_zero = 0
        for j, vj in enumerate(seq[:max_index+1]):
            r, ell = j % k, j // k
            for p in eligible:
                tested += 1
                if vj % p:
                    continue
                hits += 1
                v = (a % p, b % p)
                tau = (-1 % p, -1 % p)
                rho = qmul(qconj(v,p), qinv(v,p), p)
                rho_r = qmul(qpow(qinv(tau,p),r+3,p),rho,p)
                y = qpow(tau,ell,p)
                assert qpow(tau,j+3,p) == rho
                assert qpow(y,k,p) == rho_r
                eps = chi5(p)
                assert qpow(y,p,p) == (y if eps == 1 else qinv(y,p))
                x = qtrace(y,p)
                ar = qtrace(qmul(qmul(v,v,p), qpow(tau,r+3,p), p),p)
                dk, derivative = dickson_and_derivative(k,x,p)
                assert (norm*dk-ar) % p == 0
                discr = (ar*ar-4*norm*norm) % p
                if discr == 0:
                    trace_discriminant_zero += 1
                if norm*derivative % p == 0:
                    root_derivative_zero += 1
        results.append({
            'seed':[a,b], 'Q':norm, 'V_0':seq[0], 'V_1':seq[1],
            'max_index_inclusive':max_index,'prime_limit_inclusive':prime_limit,
            'eligible_primes':len(eligible),'integer_divisibility_checks':tested,
            'actual_divisor_hits':hits,
            'quadratic_orbit_and_Frobenius_and_Dickson_checks_passed':hits,
            'trace_discriminant_zero_hits':trace_discriminant_zero,
            'actual_trace_root_derivative_zero_hits':root_derivative_zero,
        })
    return results

def norm_family_congruence(t):
    """Finite evaluation of the exact family identity; no asymptotic inference."""
    assert isinstance(t, int) and t >= 0
    a, b = 4+361*t, 1
    norm = a*a+a*b-b*b
    expanded = 19+3249*t+130321*t*t
    assert norm == expanded
    assert norm % (19*19) == 19
    assert (a+15*b) % 19 == 0
    assert (a+5*b) % 19 == 9
    return {'t':t, 'seed':[a,b], 'Q':norm, 'Q_mod_19_squared':19,
            'v19_Q':1, 'value_at_phi_15_mod_19':0, 'value_at_phi_5_mod_19':9}

def norm_family_experiment(k=105, max_index=210, prime_limit=500):
    parameters = list(range(8))
    identity_samples = parameters + [19, 105, 10**6, 10**12]
    records = [norm_family_congruence(t) for t in identity_samples]
    seeds = [(4+361*t,1) for t in parameters]
    checks = divisor_bridge_experiment(k,seeds,max_index,prime_limit)
    return {
        'family':'v_t=(4+361t)+phi, t>=0',
        'identity':'Q_t=19+3249t+130321t^2 == 19 (mod 19^2)',
        'split_roots_mod_19':[5,15],
        'identity_samples':records,
        'source_congruence_seed_parameters':parameters,
        'source_congruences':checks,
        'total_integer_divisibility_checks':sum(r['integer_divisibility_checks'] for r in checks),
        'total_actual_divisor_hits':sum(r['actual_divisor_hits'] for r in checks),
        'total_actual_repeated_root_hits':sum(r['actual_trace_root_derivative_zero_hits'] for r in checks),
        'limitation':'These finite checks certify the evaluated identities and modular tests only; the all-t valuation statement follows from the displayed polynomial identity, not sampling.',
    }


def affine_power_mod(x, exponent, modulus):
    out = (1, 0)
    while exponent:
        if exponent & 1:
            out = qmul(out, x, modulus)
        x = qmul(x, x, modulus)
        exponent //= 2
    return out


def affine_source_norm(x):
    a, b = x
    return a*a+a*b-b*b


def affine_source_quantity(x):
    return 2*x[0]+3*x[1]


def affine_fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a+b
    return a


def affine_lucas(n):
    return trace(power((0,1),n))


def affine_zeckendorf_indices(n):
    weights = [0,1,1]
    while weights[-1] <= n:
        weights.append(weights[-2]+weights[-1])
    indices = []
    for i in range(len(weights)-1,1,-1):
        if weights[i] <= n:
            indices.append(i)
            n -= weights[i]
    assert n == 0
    assert all(a-b >= 2 for a,b in zip(indices,indices[1:]))
    return indices


def check_affine_shift_identities():
    seeds = [(1,0),(16,29),(1,4),(1,5)]
    primes = list(primes_below(501))
    square_checks = norm_checks = residue_hits = 0
    for seed in seeds:
        for j in range(17):
            a,b = power((0,1),j)
            a,b = mul((a,b),seed)
            qj = affine_source_norm((a,b))
            assert qj == (-1)**j * affine_source_norm(seed)
            u = affine_source_quantity((a,b))
            c = 4*a+7*b
            for g in range(1,6):
                n = g*u+1
                delta = 5-4*g*g*qj
                assert (g*c)**2-delta == 5*n*(n-2)
                assert gcd(n,g*u) == 1
                square_checks += 1
                for r in range(-4,5):
                    shift = (3*r-1,1-2*r)
                    y = (g*a+shift[0],g*b+shift[1])
                    expected = g*g*qj+g*(r*(4*a+7*b)-(a+3*b))-r*r+3*r-1
                    assert affine_source_quantity(y) == n and affine_source_norm(y) == expected
                    d = gcd(*y)
                    assert d > 0 and gcd(d,g) == 1
                    assert (g*g*qj+r*r-3*r+1) % d == 0
                    assert (a+b-r*u) % d == 0
                    assert affine_source_norm(y) % (d*d) == 0
                    norm_checks += 1
                for p in primes:
                    if n % p or (2*delta) % p == 0:
                        continue
                    assert pow(delta % p,(p-1)//2,p) == 1
                    residue_hits += 1
    return {'seeds':[list(x) for x in seeds],'j_inclusive':[0,16],
            'g_inclusive':[1,5],'kernel_translation_r_inclusive':[-4,4],
            'prime_limit_inclusive':500,'shifted_square_checks':square_checks,
            'translation_norm_and_content_checks':norm_checks,
            'actual_shifted_prime_quadratic_residue_hits':residue_hits}


def check_affine_old_support_counterexamples():
    seed, q, k = (16,29), -121, 105
    records = []
    for j,p in [(3,2),(4,409)]:
        x = mul(power((0,1),j),seed)
        u = affine_source_quantity(x)
        n = u+1
        ar = trace(mul(mul(seed,seed),power((-1,-1),j+3)))
        roots = [z for z in range(p) if (q*dickson_and_derivative(k,z,p)[0]-ar) % p == 0]
        assert n % p == 0 and (5*k*q) % p != 0 and not roots
        old_bits, new_bits = affine_zeckendorf_indices(u), affine_zeckendorf_indices(n)
        assert 2 not in old_bits and 3 not in old_bits
        assert new_bits == old_bits+[2]
        delta = 5-4*affine_source_norm(x)
        c = 4*x[0]+7*x[1]
        assert (c*c-delta) % p == 0
        records.append({'seed':list(seed),'j':j,'g':1,'composition':list(x),
                        'U':u,'N':n,'prime':p,'k':k,'Q_mod_p':q%p,
                        'Ar_mod_p':ar%p,'old_trace_polynomial_root_count':len(roots),
                        'old_canonical_indices':old_bits,'shifted_canonical_indices':new_bits,
                        'new_square_D':delta,'new_square_D_mod_p':delta%p,
                        'new_square_witness_mod_p':c%p})
    p = 409
    order = next(i for i in range(1,p) if affine_power_mod((0,1),i,p) == (1,0))
    period = k*order//gcd(k,order)
    assert order == 408 and period == 14280
    assert affine_power_mod((0,1),period,p) == (1,0)
    for t in [0,1,2,10,10**6]:
        j = 4+period*t
        x = mul(affine_power_mod((0,1),j,p),seed)
        assert (affine_source_quantity(x)+1) % p == 0 and j % k == 4
    return {'examples':records,'infinite_progression_certificate':{
        'seed':list(seed),'g':1,'prime':409,'phi_order_mod_p':order,
        'progression_j':'4+14280*t, t>=0','period':period,
        'progression_checks_t':[0,1,2,10,10**6],
        'scope':'The finite period identity plus multiplication proves the congruence for every t; canonical legality for all j>=3 is justified separately in the paper record.'}}


def check_affine_bounded_translation():
    bound = 6
    rows, checks = [], 0
    for j in range(3,121):
        a,b = power((0,1),j)
        n = 2*affine_source_quantity((a,b))+1
        assert affine_zeckendorf_indices(n) == [j+4,j+1,2]
        for r in range(-bound,bound+1):
            y = (2*a+3*r-1,2*b+1-2*r)
            if min(y) < 0:
                continue
            d = gcd(*y)
            c = 4*(-1)**j+r*r-3*r+1
            assert c != 0 and c % d == 0
            raw = affine_source_norm(y)
            primitive = raw // (d*d)
            assert raw % (d*d) == 0
            assert 2*abs(raw) > n
            assert 2*c*c*abs(primitive) > n
            checks += 1
        y = (2*a-1,2*b+1)
        d = gcd(*y)
        assert (5 if j%2 == 0 else 3) % d == 0
        if j in [3,4,7,8,14,24,48,96,120]:
            rows.append({'j':j,'N':n,'r':0,'new_gcd':d,'raw_norm':affine_source_norm(y),
                         'primitive_norm':affine_source_norm(y)//(d*d),
                         'abs_primitive_norm_over_N':str(Fraction(abs(affine_source_norm(y)),d*d*n))})
    return {'seed':[1,0],'g':2,'j_inclusive':[3,120],
            'kernel_translation_r_inclusive':[-bound,bound],
            'nonnegative_translation_checks':checks,
            'general_content_divisor':'d_r divides 4*(-1)^j+r^2-3r+1',
            'r0_content_divisor_even_j':5,'r0_content_divisor_odd_j':3,
            'finite_bound_used':'abs(Q_primitive)>N/(2*(4*(-1)^j+r^2-3r+1)^2)',
            'sample_rows':rows}


def check_affine_fibonacci_plus_one():
    rows = []
    for j in range(3,121):
        a = 1 if j%2 else 2
        m = (j+a)//2
        shift = (-1,1) if a==1 else (2,-1)
        original = power((0,1),j)
        y = tuple(t+s for t,s in zip(original,shift))
        if m%2 == 0:
            d, primitive = affine_lucas(m), power((0,1),m-a)
        else:
            d = affine_fib(m)
            primitive = mul((-1,2),power((0,1),m-a))
        assert min(primitive) >= 0 and gcd(*primitive) == 1
        assert y == tuple(d*t for t in primitive)
        assert gcd(*y) == d
        assert abs(affine_source_norm(primitive)) in [1,5]
        u = affine_source_quantity(primitive)
        n = affine_fib(j+3)+1
        assert affine_source_quantity(y) == n == d*u and d < 2*u
        assert affine_zeckendorf_indices(n) == [j+3,2]
        if j in [3,4,5,6,7,8,14,15]:
            rows.append({'j':j,'a':a,'m':m,'shift':list(shift),'N':n,
                         'new_multiplier':d,'primitive_composition':list(primitive),
                         'primitive_norm':affine_source_norm(primitive),'primitive_quantity':u})
    return {'seed':[1,0],'g':1,'j_inclusive':[3,120],
            'cases_checked':118,'shifts_used':[[-1,1],[2,-1]],
            'new_multiplier_bound':'d<2*q(primitive)',
            'absolute_primitive_norms':[1,5],'sample_rows':rows}


def check_unit_bit_one_affine():
    report={'purpose':'Distinguish failed old-support transfer, exact shifted character condition, bounded-translation obstruction, and an explicit successful subfamily.',
            'arithmetic':'Python 3 standard library, exact integers and fractions',
            'identities':check_affine_shift_identities(),
            'old_support_counterexamples':check_affine_old_support_counterexamples(),
            'bounded_translation_obstruction':check_affine_bounded_translation(),
            'successful_Fibonacci_plus_one_subfamily':check_affine_fibonacci_plus_one(),
            'limitations':['Finite checks are not a Robin proof.','The bounded-translation obstruction does not exclude unbounded kernel translations with growing new gcd.','The successful g=1 Fibonacci subfamily does not cover arbitrary multipliers g.']}
    return report


def affine_near_boundary_samples():
    """Exact finite CRT witnesses; integer cuts do not certify an asymptotic limit."""
    settings = [(101, 2, 148), (211, 10, 320), (401, 28, 627),
                (809, 78, 1301), (1601, 180, 2638), (3203, 418, 5398)]
    prime_indices = set(primes_below(3204))
    records = []
    for index, core_cut, rough_cut in settings:
        assert index in prime_indices and index >= 7 and core_cut < rough_cut
        fib = [0, 1]
        for _ in range(2, 2 * index + 6):
            fib.append(fib[-1] + fib[-2])
        value = fib[index]
        core = 1
        for n in range(2, core_cut + 1):
            core = core * n // gcd(core, n)
        assert gcd(core, value) == 1
        lower, upper = (value + 9) // 10, value // 5
        residue = (-pow(value, -1, core)) % core
        first_t = (lower - residue + core - 1) // core
        rough_primes = list(primes_below(rough_cut + 1))
        rough_primorial = prod(rough_primes)
        for attempt in range(100000):
            multiplier = residue + core * (first_t + attempt)
            assert multiplier <= upper
            number = multiplier * value + 1
            assert number % core == 0
            cofactor = number // core
            if gcd(cofactor, rough_primorial) == 1:
                break
        else:
            raise AssertionError('finite CRT search did not find a witness')
        assert lower <= multiplier <= upper
        assert gcd(core, cofactor) == 1
        a, b = mul((multiplier, 0), power((0, 1), index - 3))
        assert 2 * a + 3 * b + 1 == number
        assert a * a + a * b - b * b == multiplier * multiplier
        assert gcd(a, b) == multiplier
        remaining = number
        decoded_a = decoded_b = unit = 0
        selected = []
        for k in range(len(fib) - 1, 1, -1):
            if fib[k] > remaining:
                continue
            remaining -= fib[k]
            selected.append(k)
            if k == 2:
                unit = 1
            elif k == 3:
                decoded_a += 1
            else:
                decoded_a += fib[k - 4]
                decoded_b += fib[k - 3]
        assert remaining == 0 and (decoded_a, decoded_b, unit) == (a, b, 1)
        assert all(x - y >= 2 for x, y in zip(selected, selected[1:]))
        discriminant = 5 - 4 * multiplier * multiplier
        assert (4 * a + 7 * b) ** 2 - discriminant == 5 * number * (number - 2)
        shifted_norm = (a - 1) ** 2 + (a - 1) * (b + 1) - (b + 1) ** 2
        assert 10 * abs(shifted_norm) >= 3 * (number - 1) + 10
        assert abs(shifted_norm) <= number
        support_hits = 0
        for p in primes_below(2 * index - 1):
            assert value % p != 0
            g0 = (-pow(value, -1, p)) % p
            gp = g0 + p * ((lower - g0 + p - 1) // p)
            assert lower <= gp <= upper and (gp * value + 1) % p == 0
            support_hits += 1
        core_weight = Fraction(1)
        for p in primes_below(core_cut + 1):
            power_p = p
            while power_p * p <= core_cut:
                power_p *= p
            core_weight *= Fraction(p * power_p - 1, power_p * (p - 1))
        records.append({
            'prime_index': index, 'core_cutoff': core_cut,
            'rough_cutoff': rough_cut, 'search_attempts': attempt + 1,
            'integer_digits': len(str(number)),
            'integer_sha256': hashlib.sha256(str(number).encode()).hexdigest(),
            'multiplier': str(multiplier), 'core': str(core),
            'core_response': str(core_weight),
            'canonical_composition_and_unit_bit': True,
            'primitive_norm_one': True, 'coprime_core_and_rough_cofactor': True,
            'affine_square_identity': True, 'shifted_raw_norm_bounds': True,
            'all_primes_below_2r_minus_1_realized': support_hits,
        })
    return {
        'scope': 'six explicit integer-cutoff CRT witnesses; exact arithmetic only',
        'samples': records,
        'limitation': 'These finite cuts are specified inputs, not a certificate of the logarithmic cutoff formula, an asymptotic limit, or a Robin margin.',
    }


def check_unit_one_affine_sources():
    """Return exact finite diagnostics for theory section 204.

    Reuse prime_sections.py's Fraction, gcd, mul, power, trace, primes_below
    and dickson_and_derivative. All additional helpers are local; in particular
    negative exponents never reach the existing nonnegative-only power helper.
    """
    from math import isqrt

    phi = (Fraction(0), Fraction(1))
    sqrt5 = (Fraction(-1), Fraction(2))

    def add(x, y):
        return x[0] + y[0], x[1] + y[1]

    def neg(x):
        return -x[0], -x[1]

    def conjugate(x):
        return x[0] + x[1], -x[1]

    def norm(x):
        return x[0] * x[0] + x[0] * x[1] - x[1] * x[1]

    def inverse(x):
        value = norm(x)
        assert value
        return tuple(t / value for t in conjugate(x))

    def signed_power(x, exponent):
        if exponent < 0:
            return power(inverse(x), -exponent)
        return power(x, exponent)

    def scale(c, x):
        return c * x[0], c * x[1]

    def fibonacci(n):
        a, b = 0, 1
        for _ in range(n):
            a, b = b, a + b
        return a

    def shift(a, b, j):
        for _ in range(j):
            a, b = b, a + b
        return a, b

    def quantity(x):
        return 2 * x[0] + 3 * x[1]

    def greedy_source(n):
        fibs = [0, 1, 1]
        while fibs[-1] <= n:
            fibs.append(fibs[-1] + fibs[-2])
        bits = []
        for i in range(len(fibs) - 1, 1, -1):
            if fibs[i] <= n:
                n -= fibs[i]
                bits.append(i)
        assert n == 0
        assert all(a - b >= 2 for a, b in zip(bits, bits[1:]))
        composition = (0, 0)
        for i in bits:
            if i >= 3:
                term = shift(1, 0, i - 3)
                composition = add(composition, term)
        return composition, 2 in bits, not any(3 <= i <= 5 for i in bits)

    def reduce_fraction(x, p):
        assert x.denominator % p
        return x.numerator * pow(x.denominator, -1, p) % p

    def equal_at_prime(x, y, p, root):
        if root is None:
            return (tuple(reduce_fraction(t, p) for t in x) ==
                    tuple(reduce_fraction(t, p) for t in y))
        return (reduce_fraction(x[0] - y[0], p) +
                root * reduce_fraction(x[1] - y[1], p)) % p == 0

    def matrix_order(p):
        a, b, c, d = 1, 0, 0, 1
        for t in range(1, 10 * p * p + 1):
            a, b, c, d = b, (a + b) % p, d, (c + d) % p
            if (a, b, c, d) == (1, 0, 0, 1):
                return t
        raise AssertionError(('order bound', p))

    primes = list(primes_below(102))
    counts = dict(quadratic_identities=0, square_target_pairs=0,
                  norm_one_targets=0, content_nonunit_targets=0,
                  actual_prime_places=0, trace_kummer_checks=0,
                  unit_rank_checks=0, legal_all_prime_witnesses=0)
    examples = {}
    seeds = [(a, b) for a in range(13) for b in range(13)
             if (a or b) and gcd(a, b) == 1] + [(4, 21)]
    for a, b in seeds:
        seed = (Fraction(a), Fraction(b))
        seed_norm = int(norm(seed))
        for g in range(1, 13):
            for parity in (0, 1):
                first = scale(g, mul(signed_power(phi, parity + 3), seed))
                second = conjugate(first)
                discriminant = 5 + 4 * norm(first)
                assert discriminant.denominator == 1
                value = int(discriminant)
                square_root = isqrt(value) if value >= 0 else -1
                roots = []
                if square_root >= 0 and square_root * square_root == value:
                    roots = [mul((Fraction(square_root + 1, 2), Fraction(-1)),
                                 inverse(first)),
                             mul((Fraction(1 - square_root, 2), Fraction(-1)),
                                 inverse(first))]
                    assert roots[0] != roots[1]
                    counts['square_target_pairs'] += 1
                    units = []
                    for alpha in roots:
                        assert norm(alpha) == 1
                        counts['norm_one_targets'] += 1
                        unit = all(t.denominator == 1 for t in alpha)
                        units.append(unit)
                        if g > 1:
                            assert not unit
                            counts['content_nonunit_targets'] += 1
                    kind = ('g_gt_1_' if g > 1 else 'g_1_') + str(sum(units)) + '_units'
                    if kind not in examples:
                        examples[kind] = {
                            'seed': [a, b], 'g': g, 'parity': parity,
                            'Delta': value,
                            'roots': [[str(t) for t in alpha] for alpha in roots]}
                for m in range(13):
                    j = parity + 2 * m
                    number = g * (a * fibonacci(j + 3) + b * fibonacci(j + 4)) + 1
                    y = signed_power(phi, 2 * m)
                    lhs = add(add(mul(first, mul(y, y)), mul(sqrt5, y)), neg(second))
                    assert lhs == scale(number, mul(sqrt5, y))
                    counts['quadratic_identities'] += 1
                    if not roots:
                        continue
                    for p in primes:
                        if (10 * g * seed_norm) % p == 0 or number % p:
                            continue
                        residues = [z for z in range(p) if (z * z - z - 1) % p == 0]
                        assert len(residues) in (0, 2)
                        for root in residues or [None]:
                            assigned = [alpha for alpha in roots
                                        if equal_at_prime(y, alpha, p, root)]
                            assert assigned
                            counts['actual_prime_places'] += 1
                            for alpha in assigned:
                                k, remainder, quotient = 3, m % 3, m // 3
                                beta = mul(alpha, signed_power(phi, -2 * remainder))
                                target = trace(signed_power(phi, 2 * quotient))
                                assert target.denominator == 1
                                assert trace(beta).denominator % p
                                dickson, _ = dickson_and_derivative(k, int(target), p)
                                assert (dickson - reduce_fraction(trace(beta), p)) % p == 0
                                counts['trace_kummer_checks'] += 1
                                if all(t.denominator == 1 for t in alpha):
                                    matches = [(sign, t) for t in range(-25, 26)
                                               for sign in (-1, 1)
                                               if scale(sign, signed_power(phi, 2 * t)) == alpha]
                                    assert len(matches) == 1
                                    sign, t = matches[0]
                                    if m != t:
                                        assert fibonacci(2 * abs(m - t)) % p == 0
                                        counts['unit_rank_checks'] += 1

    witness_examples = []
    witness_seeds = [(1, 0), (0, 1), (1, 1), (2, 1), (16, 29), (11, 8)]
    for a, b in witness_seeds:
        for p in primes:
            first_index = 0 if (2 * a + 3 * b) % p else 1
            initial_value = quantity(shift(a, b, first_index))
            assert initial_value % p
            g = (-pow(initial_value, -1, p)) % p
            assert 1 <= g <= p - 1
            period = matrix_order(p)
            for t in range(1, 101):
                j = first_index + t * period
                aa, bb = shift(a, b, j)
                composition = (g * aa, g * bb)
                number = quantity(composition) + 1
                assert number % p == 0
                decoded, unit, null = greedy_source(number)
                if decoded == composition and unit and null:
                    break
            else:
                raise AssertionError(('no canonical witness', a, b, p))
            counts['legal_all_prime_witnesses'] += 1
            if (a, b) == (1, 0) and p in (2, 3, 5, 7, 11):
                witness_examples.append(dict(p=p, g=g, j=j, N=str(number)))

    return {
        'status': 'PASS',
        'kind': 'finite exact arithmetic diagnostics, not Lean or an infinite proof',
        'ranges': {
            'seed_coordinates': '0..12, primitive nonzero, plus (4,21) for the two-nonunit g=1 case',
            'g': '1..12', 'j': 'parities with m=0..12', 'primes': 'all primes <=101',
            'all_prime_seeds': [list(seed) for seed in witness_seeds]},
        'counts': counts, 'target_examples': examples,
        'all_prime_examples': witness_examples}


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
        'unit_bit_one_affine': check_unit_bit_one_affine(),
        'unit_one_near_boundary_samples': affine_near_boundary_samples(),
        'unit_one_fixed_parameter_sources': check_unit_one_affine_sources(),
        'cyclotomic_105': {
            'root_action': affine_experiment(105),
            'actual_divisor_checks': divisor_bridge_experiment(
                105, [(16, 29), (1, 4), (1, 5)], 420, 2000),
            'changing_norm_family': norm_family_experiment(),
        },
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'source_checks': result['source_checks'],
                      'group_windows': [row['window'] for row in result['root_groups']],
                      'general_seed_checks': result['general_seed_checks']}))


if __name__ == '__main__':
    main()
