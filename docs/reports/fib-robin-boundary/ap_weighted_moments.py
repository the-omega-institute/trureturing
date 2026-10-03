#!/usr/bin/env python3
"""Finite exact weighted moments on the actual progression N=1+g*V.

Python 3.9+ standard library only. Finite U_X is not an infinite Euler constant;
no logarithmic, asymptotic, Robin, or RH claim is evaluated.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
from math import gcd, isqrt, lcm
from pathlib import Path
import json


ORDERS = (1, 2, 3)
SCALE = 10 ** 24
SMALL_V_MAX = 12
SMALL_G0_MAX = 6
SMALL_LENGTH_MAX = 6
FIBONACCI_INDICES = (7, 11, 13, 17)
REPRESENTATIVE_SMALL = {(1, 1, 1), (2, 1, 1), (4, 1, 4),
                        (6, 2, 3), (12, 6, 6)}
CODIVISOR_INTEGERS = (2, 4, 6, 9, 12, 27, 49, 91, 121)


def fibonacci_pair(n):
    if n == 0:
        return 0, 1
    a, b = fibonacci_pair(n // 2)
    c, d = a * (2 * b - a), a * a + b * b
    return (d, c + d) if n % 2 else (c, d)


def direct_divisors(number):
    low, high = [], []
    for d in range(1, isqrt(number) + 1):
        if number % d == 0:
            low.append(d)
            if d * d != number:
                high.append(number // d)
    return low + high[::-1]


def coefficient_numerators(maximum):
    """Represent multiplicative b_k(d) as the exact integer B_k[d]/d^k."""
    smallest = [0] * (maximum + 1)
    for p in range(2, isqrt(maximum) + 1):
        if smallest[p] == 0:
            for multiple in range(p * p, maximum + 1, p):
                if smallest[multiple] == 0:
                    smallest[multiple] = p
    numerators = {k: [0] * (maximum + 1) for k in ORDERS}
    for k in ORDERS:
        numerators[k][1] = 1
    prime_power_cases = 0
    for d in range(2, maximum + 1):
        p, rest, power_p, sigma = smallest[d] or d, d, 1, 1
        while rest % p == 0:
            rest //= p
            power_p *= p
            sigma += power_p
        previous_sigma = sigma - power_p
        for k in ORDERS:
            local = sigma ** k - p ** k * previous_sigma ** k
            assert local > 0
            numerators[k][d] = numerators[k][rest] * local
        if rest == 1:
            prime_power_cases += 1
    assert all(n == 1 for n in numerators[1][1:])
    return numerators, prime_power_cases


def outward(numerator, denominator):
    assert denominator > 0
    lo, remainder = divmod(numerator * SCALE, denominator)
    return lo, lo + int(remainder != 0)


def interval(pair):
    return Fraction(pair[0], SCALE), Fraction(pair[1], SCALE)


def render(bounds):
    lo, hi = bounds
    assert lo <= hi
    return {'lower': str(lo), 'upper': str(hi), 'width': str(hi - lo)}


def add_pair(target, pair):
    target[0] += pair[0]
    target[1] += pair[1]


def difference(whole, part):
    return whole[0] - part[1], whole[1] - part[0]


def ratio(numerator, denominator):
    assert 0 <= numerator[0] <= numerator[1] and 0 < denominator[0]
    lo, hi = numerator[0] / denominator[1], numerator[1] / denominator[0]
    assert lo <= 1
    return lo, min(Fraction(1), hi)


def sign(bounds):
    if bounds[0] > 0:
        return 'positive'
    if bounds[1] < 0:
        return 'negative'
    if bounds == (0, 0):
        return 'zero'
    return 'unresolved_by_enclosure'


def count_residue(V, G0, G1, d):
    if gcd(V, d) != 1:
        return 0
    residue = (-pow(V, -1, d)) % d
    return (G1 - residue) // d - (G0 - 1 - residue) // d


def canonical_unit_source(r, g, number):
    A, B = fibonacci_pair(r - 4)
    a, b = g * A, g * B
    assert gcd(A, B) == 1 and A * A + A * B - B * B == 1
    assert 2 * a + 3 * b + 1 == number
    weights = [0, 1, 1]
    while weights[-1] <= number:
        weights.append(weights[-2] + weights[-1])
    remaining, chosen = number, []
    for j in range(len(weights) - 1, 1, -1):
        if weights[j] <= remaining:
            remaining -= weights[j]
            chosen.append(j)
    assert remaining == 0 and all(x - y >= 2 for x, y in zip(chosen, chosen[1:]))
    aa = bb = bit = 0
    for j in chosen:
        if j == 2:
            bit = 1
        elif j == 3:
            aa += 1
        else:
            aa += weights[j - 4]
            bb += weights[j - 3]
    assert (aa, bb, bit) == (a, b, 1)
    return {'composition': [a, b], 'unit_bit': bit, 'indices': chosen}


def codivisor_certificate(numerators):
    """Independent ordered-divisor expansion grouped by their common lcm."""
    rows = []
    for number in CODIVISOR_INTEGERS:
        divisors = direct_divisors(number)
        sigma = sum(divisors)
        assert sum(number // d for d in divisors) == sigma
        coefficients, digest = {1: 1}, hashlib.sha256()
        for k in ORDERS:
            next_coefficients = {}
            for ell, weight in coefficients.items():
                for d in divisors:
                    common = lcm(ell, d)
                    next_coefficients[common] = (next_coefficients.get(common, 0)
                                                 + weight * (number // d))
            coefficients = next_coefficients
            assert sum(coefficients.values()) == sigma ** k
            for ell in divisors:
                assert coefficients[ell] * ell ** k == numerators[k][ell] * number ** k
                digest.update(f'{k},{ell},{coefficients[ell]}\n'.encode())
        rows.append({'N': number, 'divisor_count': len(divisors),
                     'Z_exact': str(Fraction(sigma, number)),
                     'orders': list(ORDERS), 'grouped_coefficient_sha256': digest.hexdigest()})
    return {'method': 'Independent integer-weighted ordered divisor convolution, grouped by lcm; coefficients equal b_k(ell), and their sum equals the direct Z(N)^k.',
            'representatives': rows}


def case(V, G0, length, numerators, exact_finite_sum, r=None):
    G1, X = G0 + length - 1, V * (G0 + length - 1) + 1
    numbers = [1 + g * V for g in range(G0, G1 + 1)]
    divisors = [direct_divisors(n) for n in numbers]
    sigmas = [sum(ds) for ds in divisors]
    actual_hits = {}
    denominator = 1
    for n, ds in zip(numbers, divisors):
        denominator = lcm(denominator, n)
        assert sum(n // d for d in ds) == sum(ds)
        for d in ds:
            actual_hits[d] = actual_hits.get(d, 0) + 1
    sources = []
    if r is not None:
        assert fibonacci_pair(r)[0] == V
        for g, n in zip(range(G0, G1 + 1), numbers):
            sources.append(canonical_unit_source(r, g, n))
    cuts = sorted({min(X, max(1, d)) for d in
                   (1, length, V, isqrt(X), X // 4, X // 2, X)})
    common = lcm(*range(1, X + 1)) if exact_finite_sum else None
    records, scalar_values = [], {}
    count_summary = {'positive_hit_moduli': 0, 'noncoprime_moduli': 0,
                     'd_gt_interval_length_hits': 0, 'd_gt_interval_length_misses': 0}
    maximum_K = (0, 1)
    for k in ORDERS:
        actual_moment_numerator = sum(s ** k * (denominator // n) ** k
                                      for s, n in zip(sigmas, numbers))
        moment_denominator = denominator ** k
        weighted_numerator = 0
        u, uc, boundary, positive, negative = [0, 0], [0, 0], [0, 0], [0, 0], [0, 0]
        mass_bins = [[0, 0] for _ in range(5)]
        exact_u = exact_uc = 0
        snapshots = {}
        positive_extreme = negative_extreme = None
        for d in range(1, X + 1):
            coprime = gcd(d, V) == 1
            hits = actual_hits.get(d, 0)
            assert hits == count_residue(V, G0, G1, d)
            assert 0 <= d * hits <= X
            if k == 1:
                count_summary['positive_hit_moduli'] += hits > 0
                count_summary['noncoprime_moduli'] += not coprime
                if d > length:
                    assert hits <= 1
                    count_summary['d_gt_interval_length_hits'] += hits == 1
                    count_summary['d_gt_interval_length_misses'] += hits == 0
                if d * hits * maximum_K[1] > maximum_K[0] * X:
                    maximum_K = (d * hits, X)
            bn = numerators[k][d]
            unit_denominator = d ** (k + 1)
            weight_pair = outward(bn, unit_denominator)
            add_pair(u, weight_pair)
            bin_index = min(4, (4 * d * hits) // X)
            add_pair(mass_bins[bin_index], weight_pair)
            if common is not None:
                contribution = bn * (common // d) ** (k + 1)
                exact_u += contribution
            if coprime:
                assert abs(d * hits - length) <= d
                add_pair(uc, weight_pair)
                if common is not None:
                    exact_uc += contribution
                boundary_num = bn * (d * hits - length)
                term_pair = outward(boundary_num, unit_denominator)
                add_pair(boundary, term_pair)
                if boundary_num > 0:
                    add_pair(positive, term_pair)
                    if (positive_extreme is None or boundary_num * positive_extreme[2]
                            > positive_extreme[1] * unit_denominator):
                        positive_extreme = (d, boundary_num, unit_denominator, hits)
                elif boundary_num < 0:
                    add_pair(negative, term_pair)
                    if (negative_extreme is None or boundary_num * negative_extreme[2]
                            < negative_extreme[1] * unit_denominator):
                        negative_extreme = (d, boundary_num, unit_denominator, hits)
            if hits:
                assert denominator % d == 0
                weighted_numerator += hits * bn * (denominator // d) ** k
            if d in cuts:
                snapshots[d] = (tuple(u), tuple(uc), tuple(boundary),
                                weighted_numerator, exact_u, exact_uc)
        assert weighted_numerator == actual_moment_numerator
        exact_M = Fraction(actual_moment_numerator, moment_denominator)
        moment_interval = interval(outward(actual_moment_numerator, moment_denominator))
        u_interval, uc_interval = interval(u), interval(uc)
        boundary_interval = interval(boundary)
        exact_B = None
        if common is not None:
            exact_U = Fraction(exact_u, common ** (k + 1))
            exact_Uc = Fraction(exact_uc, common ** (k + 1))
            exact_B = exact_M - length * exact_Uc
            assert u_interval[0] <= exact_U <= u_interval[1]
            assert uc_interval[0] <= exact_Uc <= uc_interval[1]
            assert boundary_interval[0] <= exact_B <= boundary_interval[1]
            boundary_interval = (exact_B, exact_B)
        relation = (exact_M - length * uc_interval[1],
                    exact_M - length * uc_interval[0])
        assert max(relation[0], boundary_interval[0]) <= min(relation[1], boundary_interval[1])
        assert u_interval[1] - u_interval[0] <= Fraction(X, SCALE)
        assert boundary_interval[1] - boundary_interval[0] <= Fraction(X, SCALE)
        splits = []
        for D in cuts:
            up, ucp, bp, wp, eup, eucp = snapshots[D]
            left_U = interval(up)
            left_M = interval(outward(wp, moment_denominator))
            left_B = interval(bp)
            if common is not None:
                exact_left_B = Fraction(wp, moment_denominator) - length * Fraction(eucp, common ** (k + 1))
                left_B = (exact_left_B, exact_left_B)
            right_U = difference(u_interval, left_U)
            right_U = max(Fraction(0), right_U[0]), max(Fraction(0), right_U[1])
            right_M = interval(outward(actual_moment_numerator - wp, moment_denominator))
            right_B = difference(boundary_interval, left_B)
            mass_left, mass_right = ratio(left_U, u_interval), ratio(right_U, u_interval)
            moment_left, moment_right = ratio(left_M, moment_interval), ratio(right_M, moment_interval)
            if D == X:
                mass_left = moment_left = (Fraction(1), Fraction(1))
                mass_right = moment_right = right_B = (Fraction(0), Fraction(0))
            splits.append({'D': D,
                           'finite_U_mass_left': render(mass_left),
                           'finite_U_mass_right': render(mass_right),
                           'moment_fraction_left': render(moment_left),
                           'moment_fraction_right': render(moment_right),
                           'boundary_left': render(left_B), 'boundary_right': render(right_B),
                           'boundary_left_sign': sign(left_B), 'boundary_right_sign': sign(right_B)})
        def term_record(term):
            if term is None:
                return None
            d, numerator, divisor, hits = term
            return {'d': d, 'A_I_d': hits, 'K_exact': str(Fraction(d * hits, X)),
                    'b_k_d_exact': str(Fraction(numerators[k][d], d ** k)),
                    'boundary_term_exact': str(Fraction(numerator, divisor))}
        signature = f'{actual_moment_numerator}/{moment_denominator}\n'
        records.append({'k': k,
                        'M_sum': render(moment_interval),
                        'M_exact_signature_sha256': hashlib.sha256(signature.encode()).hexdigest(),
                        'U_X_all_d': render(u_interval), 'U_X_coprime_to_V': render(uc_interval),
                        'finite_mu_coprime_mass': render(ratio(uc_interval, u_interval)),
                        'finite_mu_mean_K': render(ratio((moment_interval[0] / X, moment_interval[1] / X), u_interval)),
                        'K_bin_finite_mu_masses': [render(ratio(interval(b), u_interval)) for b in mass_bins],
                        'B_X': render(boundary_interval), 'B_X_sign': sign(boundary_interval),
                        'B_X_sign_scope': 'Finite boundary only; a positive sign does not certify the infinite boundary.',
                        'B_positive_terms': render(interval(positive)),
                        'B_negative_terms': render(interval(negative)),
                        'largest_positive_boundary_term': term_record(positive_extreme),
                        'most_negative_boundary_term': term_record(negative_extreme),
                        'splits': splits})
        if k == 1:
            infinite_bounds = (boundary_interval[0] - Fraction(length, X), boundary_interval[1])
            infinite_sign = sign(infinite_bounds)
            records[-1]['k1_infinite_B_certificate'] = {
                'bounds': render(infinite_bounds),
                'sign': infinite_sign if infinite_sign in ('positive', 'negative') else 'unknown',
                'tail_upper_bound': str(Fraction(length, X)),
                'justification': 'b_1(d)=1/d; 0<=T*sum_{d>X,gcd(d,V)=1}1/d^2<=T/X; B_infinite=B_X-tail.'}
        scalar_values[k] = exact_B
    digest = hashlib.sha256()
    for g, n, s in zip(range(G0, G1 + 1), numbers, sigmas):
        digest.update(f'{g},{n},{s}\n'.encode())
    row = {'V': V, 'g_interval_inclusive': [G0, G1], 'T': length, 'X': X,
           'actual_N_sigma_sha256': digest.hexdigest(), 'divisor_hit_counts': count_summary,
           'maximum_K': str(Fraction(*maximum_K)), 'orders': records}
    if r is not None:
        row['prime_index'] = r
        row['canonical_unit_one_sources_checked'] = len(sources)
        row['source_representatives'] = [dict(g=G0, N=numbers[0], **sources[0])]
        if length > 1:
            row['source_representatives'].append(dict(g=G1, N=numbers[-1], **sources[-1]))
    return row, scalar_values


def run_experiment():
    real_inputs = []
    for r in FIBONACCI_INDICES:
        V = fibonacci_pair(r)[0]
        lo, hi = (V + 9) // 10, V // 5
        real_inputs.append((r, V, lo, hi - lo + 1))
    maximum_X = max(V * (G0 + T - 1) + 1 for _, V, G0, T in real_inputs)
    numerators, prime_powers = coefficient_numerators(maximum_X)
    codivisors = codivisor_certificate(numerators)
    local_coefficients = []
    for p in (2, 3, 5):
        for exponent in (1, 2, 3):
            number, previous = p ** exponent, p ** (exponent - 1)
            z = sum((Fraction(1, d) for d in direct_divisors(number)), Fraction(0))
            before = sum((Fraction(1, d) for d in direct_divisors(previous)), Fraction(0))
            values = {}
            for k in ORDERS:
                value = Fraction(numerators[k][number], number ** k)
                assert value == z ** k - before ** k > 0
                values[k] = str(value)
            local_coefficients.append({'p': p, 'a': exponent, 'Z_prime_power': str(z),
                                       'Z_previous_power': str(before), 'b_by_order': values})
    small_digest = hashlib.sha256()
    small_rows = []
    summaries = {k: {'sign_counts': {}, 'minimum_B': None, 'maximum_B': None,
                     'minimum_B_per_T': None, 'maximum_B_per_T': None,
                     'split_opposite_sign_cases': 0} for k in ORDERS}
    summaries[1]['k1_infinite_B_sign_counts'] = {}
    extremes = {k: {} for k in ORDERS}
    number_of_cases = 0
    for V in range(1, SMALL_V_MAX + 1):
        for G0 in range(1, SMALL_G0_MAX + 1):
            for T in range(1, SMALL_LENGTH_MAX + 1):
                row, values = case(V, G0, T, numerators, True)
                number_of_cases += 1
                small_digest.update(json.dumps(row, sort_keys=True, separators=(',', ':')).encode())
                small_digest.update(b'\n')
                if (V, G0, T) in REPRESENTATIVE_SMALL:
                    small_rows.append(row)
                for record in row['orders']:
                    k, B = record['k'], values[record['k']]
                    summary = summaries[k]
                    tag = record['B_X_sign']
                    summary['sign_counts'][tag] = summary['sign_counts'].get(tag, 0) + 1
                    if k == 1:
                        infinite_tag = record['k1_infinite_B_certificate']['sign']
                        counts = summary['k1_infinite_B_sign_counts']
                        counts[infinite_tag] = counts.get(infinite_tag, 0) + 1
                    if any(s['boundary_left_sign'] in ('positive', 'negative') and
                           s['boundary_right_sign'] in ('positive', 'negative') and
                           s['boundary_left_sign'] != s['boundary_right_sign'] for s in record['splits']):
                        summary['split_opposite_sign_cases'] += 1
                    for name, val, direction in [('minimum_B', B, -1), ('maximum_B', B, 1),
                                                 ('minimum_B_per_T', B / T, -1), ('maximum_B_per_T', B / T, 1)]:
                        if name not in extremes[k] or direction * val > direction * extremes[k][name][0]:
                            extremes[k][name] = (val, {'V': V, 'G0': G0, 'T': T, 'X': row['X'],
                                                       'value_exact': str(val), 'order_record': record})
    for k in ORDERS:
        for name, (_, witness) in extremes[k].items():
            summaries[k][name] = witness
        assert summaries[k]['sign_counts'].get('positive', 0)
        assert summaries[k]['sign_counts'].get('negative', 0)
    real_rows = [case(V, G0, T, numerators, False, r)[0] for r, V, G0, T in real_inputs]
    return {
        'scope': 'Finite actual-AP weighted moments and signed boundaries, with elementary k=1 infinite-tail certificates; no higher-moment infinite sign or Robin conclusion.',
        'definitions': {
            'Z_n': 'sum_{d|n} 1/d = sigma(n)/n',
            'b_k_1': '1', 'b_k_prime_power': 'Z(p^a)^k-Z(p^(a-1))^k for a>=1; multiplicatively extended',
            'I': 'all integers g in [G0,G1], T=G1-G0+1', 'X': '1+V*G1',
            'A_I_d': '#{g in I: d divides 1+g*V}',
            'M': 'sum_{g in I} Z(1+g*V)^k = sum_{d<=X} b_k(d)*A_I(d)',
            'U_X': 'sum_{1<=d<=X} b_k(d)/d; finite, includes all d, not an infinite U',
            'U_X_coprime': 'sum_{d<=X, gcd(d,V)=1} b_k(d)/d',
            'mu_X_d': '(b_k(d)/d)/U_X on 1<=d<=X',
            'K': 'd*A_I(d)/X', 'finite_mu_mean_K': 'M/(X*U_X)',
            'finite_mu_coprime_mass': 'U_X_coprime/U_X',
            'centered_boundary_identity': 'B_X/(X*U_X)=E_mu_X[K-(T/X)*1_(gcd(d,V)=1)]; centering uses the coprime indicator.',
            'B_X': 'M-T*U_X_coprime; signed, not assumed to have mean zero',
            'infinite_B_relation': 'B_infinite=B_X-T*sum_{d>X,gcd(d,V)=1}b_k(d)/d. The nonnegative omitted tail prevents inferring positive B_infinite from positive B_X.',
            'k1_infinite_B': 'Only for k=1: b_1(d)=1/d gives B_infinite in [B_X-T/X,B_X]; report a sign only if the whole interval has that sign.',
            'K_bins': ['[0,1/4)', '[1/4,1/2)', '[1/2,3/4)', '[3/4,1)', '{1}'],
            'D_choices': 'distinct clamped integers among 1,T,V,isqrt(X),X//4,X//2,X'},
        'precision': {'per_term_denominator': SCALE,
                      'method': 'Each rational term is rounded outward using integer divmod. All finite sum enclosures are rigorous; no float is used.',
                      'U_and_B_raw_width_bound': 'X/10^24; boundary splits formed by subtraction can have larger reported widths',
                      'small_B': 'exact rational, using a common denominator for d<=X',
                      'M_identity': 'verified exactly before rounding, with common denominator lcm(N_g)^k'},
        'coefficient_table': {'maximum_d': maximum_X, 'orders': list(ORDERS),
                              'prime_power_inputs': prime_powers,
                              'local_representatives': local_coefficients,
                              'k1_identity': 'b_1(d)=1/d, checked on the complete finite table'},
        'independent_codivisor_expansion': codivisors,
        'small_intervals': {'ranges': {'V': [1, SMALL_V_MAX], 'G0': [1, SMALL_G0_MAX],
                                      'T': [1, SMALL_LENGTH_MAX]},
                            'case_count': number_of_cases, 'maximum_X': SMALL_V_MAX * (SMALL_G0_MAX + SMALL_LENGTH_MAX - 1) + 1,
                            'all_case_summary_sha256': small_digest.hexdigest(),
                            'by_order': summaries, 'representative_intervals': small_rows},
        'fibonacci_intervals': real_rows,
        'limitations': ['All normalizers and divisor sums are truncated at the explicitly recorded X.',
                        'B_X signs are finite. Only the explicitly marked k=1 certificate controls the omitted infinite tail; no k=2 or k=3 infinite sign is reported.',
                        'The Fibonacci cases cover their full stated multiplier intervals only.',
                        'No Euler-gamma, logarithmic budget, general asymptotic moment theorem, Robin margin, or RH comparison is certified.']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        parser.error('optimized execution disables exact checks')
    source = Path(__file__).resolve()
    if args.out.resolve() == source or (args.out.exists() and args.out.samefile(source)):
        parser.error('output must not overwrite this program')
    result = run_experiment()
    result['source_sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'small_intervals': result['small_intervals']['case_count'],
                      'fibonacci_integers': sum(row['T'] for row in result['fibonacci_intervals']),
                      'maximum_X': result['coefficient_table']['maximum_d'],
                      'boundary_sign_counts': {k: v['sign_counts'] for k, v in result['small_intervals']['by_order'].items()},
                      'source_sha256': result['source_sha256']}))


if __name__ == '__main__':
    main()
