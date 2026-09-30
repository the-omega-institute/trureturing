#!/usr/bin/env python3
"""Exact finite prime-section diagnostics for FIB theory sections 196–200.

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
