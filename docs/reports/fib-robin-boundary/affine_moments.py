#!/usr/bin/env python3
"""Exact finite affine divisor moments and shared-lcm counting checks.

Python 3.9+ and its standard library suffice. The fixed finite inputs do not
certify Euler constants, logarithmic cutoffs, asymptotic limits, or Robin.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from itertools import product
import json
from math import gcd, isqrt, lcm, prod
from pathlib import Path


FIBONACCI_SETTINGS = ((7, 8), (11, 13), (13, 16), (17, 22),
                      (19, 24), (23, 30), (29, 39), (31, 42))
MOMENT_ORDERS = (1, 2, 3)
ROUNDING_DENOMINATOR = 10 ** 12
EXPECTED_INTEGER_COUNT = 189527


def primes_upto(limit):
    sieve = bytearray(b'\x01') * (limit + 1)
    sieve[:min(2, limit + 1)] = b'\x00' * min(2, limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p::p] = b'\x00' * ((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def fibonacci(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def fibonacci_pair(n):
    """Independent fast-doubling reconstruction of (F_n, F_(n+1))."""
    if n == 0:
        return 0, 1
    a, b = fibonacci_pair(n // 2)
    c, d = a * (2 * b - a), a * a + b * b
    return (d, c + d) if n % 2 else (c, d)


def trial_factorization(n):
    """Independent trial division, used only for retained representatives."""
    assert n >= 1
    remaining, factors = n, []
    divisor = 2
    while divisor * divisor <= remaining:
        exponent = 0
        while remaining % divisor == 0:
            remaining //= divisor
            exponent += 1
        if exponent:
            factors.append((divisor, exponent))
        divisor = 3 if divisor == 2 else divisor + 2
    if remaining > 1:
        factors.append((remaining, 1))
    assert prod(p ** e for p, e in factors) == n
    return factors


def factor_statistics(factors, cutoff):
    sigma, core, radical = 1, 1, 1
    for p, exponent in factors:
        prime_power = p ** exponent
        sigma *= (prime_power * p - 1) // (p - 1)
        if p <= cutoff:
            core *= prime_power
            radical *= p
    return sigma, core, radical


def canonical_source(r, g, number):
    """Reconstruct the prescribed pair, then decode N independently."""
    V = fibonacci_pair(r)[0]
    A, B = fibonacci_pair(r - 4)
    assert gcd(A, B) == 1 and A * A + A * B - B * B == 1
    a, b = g * A, g * B
    assert number == g * V + 1 == 2 * a + 3 * b + 1
    assert (V + 9) // 10 <= g <= V // 5
    weights = [0, 1, 1]
    while weights[-1] <= number:
        weights.append(weights[-1] + weights[-2])
    remaining, indices = number, []
    for k in range(len(weights) - 1, 1, -1):
        if weights[k] <= remaining:
            remaining -= weights[k]
            indices.append(k)
    assert remaining == 0
    assert all(x - y >= 2 for x, y in zip(indices, indices[1:]))
    decoded_a = decoded_b = unit_bit = 0
    for k in indices:
        if k == 2:
            unit_bit = 1
        elif k == 3:
            decoded_a += 1
        else:
            decoded_a += weights[k - 4]
            decoded_b += weights[k - 3]
    assert (decoded_a, decoded_b, unit_bit) == (a, b, 1)
    return {'composition': [a, b], 'primitive_composition': [A, B],
            'primitive_norm': 1, 'coordinate_gcd': gcd(a, b),
            'unit_bit': unit_bit, 'greedy_fibonacci_indices': indices}


def outward_power(sigma, number, order, scale):
    """Enclose (sigma/number)^order with denominator scale."""
    numerator, denominator = sigma ** order * scale, number ** order
    lower, remainder = divmod(numerator, denominator)
    upper = lower + int(remainder != 0)
    assert lower * denominator <= numerator <= upper * denominator
    return lower, upper


def fibonacci_interval(r, cutoff):
    V = fibonacci(r)
    lower, upper = (V + 9) // 10, V // 5
    count, maximum = upper - lower + 1, upper * V + 1
    assert count > 0 and r in primes_upto(r)
    numbers = [g * V + 1 for g in range(lower, upper + 1)]
    residuals = numbers.copy()
    sigmas, cores, radicals = [1] * count, [1] * count, [1] * count
    for p in primes_upto(isqrt(maximum)):
        if V % p == 0:
            continue
        residue = (-pow(V, -1, p)) % p
        first_index = (residue - lower) % p
        for i in range(first_index, count, p):
            prime_power = 1
            while residuals[i] % p == 0:
                residuals[i] //= p
                prime_power *= p
            assert prime_power > 1
            sigmas[i] *= (prime_power * p - 1) // (p - 1)
            if p <= cutoff:
                cores[i] *= prime_power
                radicals[i] *= p
    for i, remaining in enumerate(residuals):
        if remaining > 1:
            sigmas[i] *= remaining + 1
            if remaining <= cutoff:
                cores[i] *= remaining
                radicals[i] *= remaining
    endpoint_sums = {k: [0, 0] for k in MOMENT_ORDERS}
    greatest_core = greatest_radical = greatest_response = 0
    core_exceeds_V = radical_exceeds_V = 0
    digest = hashlib.sha256()
    for i, number in enumerate(numbers):
        assert number % cores[i] == 0
        assert cores[i] % radicals[i] == 0
        assert gcd(cores[i], number // cores[i]) == 1
        for k in MOMENT_ORDERS:
            lo, hi = outward_power(sigmas[i], number, k, ROUNDING_DENOMINATOR)
            endpoint_sums[k][0] += lo
            endpoint_sums[k][1] += hi
        if cores[i] > cores[greatest_core]:
            greatest_core = i
        if radicals[i] > radicals[greatest_radical]:
            greatest_radical = i
        if sigmas[i] * numbers[greatest_response] > sigmas[greatest_response] * number:
            greatest_response = i
        core_exceeds_V += cores[i] > V
        radical_exceeds_V += radicals[i] > V
        digest.update(f'{lower+i},{number},{sigmas[i]},{cores[i]},{radicals[i]}\n'.encode())
    moments = []
    for k in MOMENT_ORDERS:
        lo_sum, hi_sum = endpoint_sums[k]
        denominator = count * ROUNDING_DENOMINATOR
        assert 0 <= hi_sum - lo_sum <= count
        moments.append({'order': k, 'lower': str(Fraction(lo_sum, denominator)),
                        'upper': str(Fraction(hi_sum, denominator)),
                        'width': str(Fraction(hi_sum - lo_sum, denominator))})
    representatives = {'first': 0, 'last': count - 1, 'largest_core': greatest_core,
                       'largest_radical': greatest_radical, 'largest_Z': greatest_response}
    if r == 29:
        representatives['pointwise_core_counterexample'] = 75085 - lower
    witnesses = {}
    for label, i in representatives.items():
        g, number = lower + i, numbers[i]
        factors = trial_factorization(number)
        sigma, core, radical = factor_statistics(factors, cutoff)
        assert (sigma, core, radical) == (sigmas[i], cores[i], radicals[i])
        witnesses[label] = {'g': g, 'N': number, 'factorization': factors,
                            'sigma': sigma, 'Z_exact': str(Fraction(sigma, number)),
                            'core': core, 'radical': radical,
                            'source': canonical_source(r, g, number)}
    return {'prime_index': r, 'V': V, 'g_interval_inclusive': [lower, upper],
            'integer_count': count, 'maximum_N': maximum,
            'integer_core_cutoff': cutoff, 'moments': moments,
            'core_gt_V_count': core_exceeds_V, 'radical_gt_V_count': radical_exceeds_V,
            'enumeration_sha256': digest.hexdigest(), 'witnesses': witnesses}


def residue_count(V, G0, G1, modulus):
    assert modulus >= 1
    if gcd(V, modulus) != 1:
        return 0
    residue = (-pow(V, -1, modulus)) % modulus
    return (G1 - residue) // modulus - (G0 - 1 - residue) // modulus


def joint_lcm_checks():
    """All ordered divisor tuples in 96 small actual affine intervals."""
    rows, tuple_count, blocked_count = [], 0, 0
    large_modulus_hits = large_modulus_misses = 0
    independent_product_disagreements = 0
    for V, G0, length in product(range(1, 7), range(1, 5), range(1, 5)):
        G1, X = G0 + length - 1, V * (G0 + length - 1) + 1
        numbers = [g * V + 1 for g in range(G0, G1 + 1)]
        common_denominator = lcm(*range(1, X + 1))
        weights = {d: common_denominator // d for d in range(1, X + 1)}
        masks = {d: sum((1 << i) for i, n in enumerate(numbers) if n % d == 0)
                 for d in range(1, X + 1)}
        harmonic_scaled = sum(weights.values())
        responses = [sum((Fraction(1, d) for d in range(1, n + 1) if n % d == 0),
                         Fraction(0)) for n in numbers]
        moments = []
        count_cache = {}
        for k in MOMENT_ORDERS:
            actual_scaled = expected_scaled = 0
            for divisors in product(range(1, X + 1), repeat=k):
                modulus = lcm(*divisors)
                mask, weight = (1 << length) - 1, 1
                for d in divisors:
                    mask &= masks[d]
                    weight *= weights[d]
                actual = bin(mask).count('1')
                if modulus not in count_cache:
                    count_cache[modulus] = residue_count(V, G0, G1, modulus)
                assert actual == count_cache[modulus]
                coprime = gcd(modulus, V) == 1
                if coprime:
                    assert abs(actual * modulus - length) <= modulus
                    expected_scaled += weight * (common_denominator // modulus)
                else:
                    assert actual == 0
                    blocked_count += 1
                if modulus > length:
                    assert actual <= 1
                    large_modulus_hits += actual == 1
                    large_modulus_misses += actual == 0
                if k >= 2 and coprime and prod(divisors) != modulus:
                    independent_product_disagreements += 1
                actual_scaled += weight * actual
                tuple_count += 1
            actual_moment = Fraction(actual_scaled, length * common_denominator ** k)
            direct_moment = sum((z ** k for z in responses), Fraction(0)) / length
            assert actual_moment == direct_moment
            expected = Fraction(expected_scaled, common_denominator ** (k + 1))
            bound = Fraction(harmonic_scaled ** k, length * common_denominator ** k)
            error = abs(actual_moment - expected)
            assert error <= bound
            moments.append({'order': k, 'actual_moment': str(actual_moment),
                            'truncated_joint_sum': str(expected),
                            'absolute_error': str(error), 'harmonic_error_bound': str(bound)})
        rows.append({'V': V, 'g_interval_inclusive': [G0, G1], 'X': X,
                     'integer_count': length, 'moments': moments})
    assert len(rows) == 96 and tuple_count == 779360
    assert blocked_count and large_modulus_hits and large_modulus_misses
    assert independent_product_disagreements
    return {
        'ranges': {'V_inclusive': [1, 6], 'G0_inclusive': [1, 4],
                   'interval_lengths_inclusive': [1, 4], 'orders': list(MOMENT_ORDERS),
                   'divisors': 'all ordered tuples in [1,X]^k, X=V*G1+1', 'maximum_X': 43},
        'interval_cases': len(rows), 'ordered_tuples_checked': tuple_count,
        'noncoprime_joint_tuples': blocked_count,
        'modulus_gt_interval_length_hits': large_modulus_hits,
        'modulus_gt_interval_length_misses': large_modulus_misses,
        'coprime_tuples_with_lcm_not_product': independent_product_disagreements,
        'counting_method': 'Intersect actual divisor incidence masks, compare with the one-residue floor formula, then sum exact rational joint moments.',
        'rows': rows}


def core_counterexample(rows):
    row = next(row for row in rows if row['prime_index'] == 29)
    witness = row['witnesses']['pointwise_core_counterexample']
    assert row['V'] == 514229 and witness['g'] == 75085
    assert witness['N'] == 38610884466
    assert witness['factorization'] == [(2, 1), (3, 4), (7, 2), (11, 1),
                                        (17, 1), (19, 1), (37, 2)]
    assert witness['source']['composition'] == [5633252125, 9114793405]
    assert witness['source']['unit_bit'] == 1
    assert witness['core'] == witness['N'] > row['V']
    assert witness['radical'] == 5521362 > row['V']
    count = residue_count(row['V'], *row['g_interval_inclusive'], witness['core'])
    assert witness['core'] > row['integer_count'] and count == 1
    return {'prime_index': 29, 'V': row['V'], 'integer_core_cutoff': 39,
            'witness': witness, 'core_modulus_interval_hits': count,
            'scope': 'Refutes pointwise C_39(N)<=V and R_39(N)<=V for this actual source; not an asymptotic or Robin counterexample.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        parser.error('optimized execution disables exact checks')
    source = Path(__file__).resolve()
    if args.out.resolve() == source or (args.out.exists() and args.out.samefile(source)):
        parser.error('output must not overwrite this program')
    rows = [fibonacci_interval(r, cutoff) for r, cutoff in FIBONACCI_SETTINGS]
    assert sum(row['integer_count'] for row in rows) == EXPECTED_INTEGER_COUNT
    joint = joint_lcm_checks()
    result = {
        'scope': 'Finite exact affine divisor moments, joint-lcm counts, and a pointwise core counterexample; no analytic or Lean proof.',
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'arithmetic': 'Python 3.9+ standard-library integers and rational numbers; no floating point.',
        'fibonacci_settings': [{'prime_index': r, 'integer_core_cutoff': y}
                               for r, y in FIBONACCI_SETTINGS],
        'total_actual_integers': EXPECTED_INTEGER_COUNT,
        'moment_enclosure': {
            'orders': list(MOMENT_ORDERS), 'per_sample_denominator': ROUNDING_DENOMINATOR,
            'method': 'For each exact (sigma(N)/N)^k, sum floor(Q*x) and ceil(Q*x); divide the totals by Q*T.',
            'maximum_mean_interval_width': str(Fraction(1, ROUNDING_DENOMINATOR)),
            'inequalities': 'lower <= (1/T)*sum_g Z(g*V+1)^k <= upper'},
        'enumeration_digest_columns': 'g,N,sigma(N),C_y(N),R_y(N), in increasing g, comma-separated, one newline per row',
        'fibonacci_intervals': rows, 'joint_lcm_checks': joint,
        'pointwise_core_counterexample': core_counterexample(rows),
        'limitations': [
            'The integer cutoffs are fixed input choices, not certified evaluations of a logarithmic formula.',
            'Only representatives are independently greedy-decoded; the exact enumerated integer ranges are stated separately.',
            'Finite moments and joint counts do not certify limiting Euler constants or an infinite-family theorem.',
            'No Euler-gamma, logarithmic Robin budget, Robin margin, or RH claim is computed.']}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'actual_integers': EXPECTED_INTEGER_COUNT,
                      'fibonacci_intervals': len(rows),
                      'joint_intervals': joint['interval_cases'],
                      'joint_ordered_tuples': joint['ordered_tuples_checked'],
                      'source_sha256': result['source_sha256']}))


if __name__ == '__main__':
    main()
