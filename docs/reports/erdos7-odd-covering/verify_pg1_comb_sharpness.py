#!/usr/bin/env python3
"""Exact finite-height sharpness of the current-prime cap on the PG1 law.

For fixed old forbidden and test cylinders at every depth, a disjoint
prefix comb attains the mixed-union bound and every test-pair cap together.
Old cylinders may vary with depth. The hypothesis is K <= p-3, where K is
the number of available nonunit old divisors; here M=315 and K=11.

Large heights are checked by finite prefix arithmetic, never by expanding
p**H points. Heights 1 and 2 also have independent literal CRT/kernel sums,
including alternate forbidden/test prefixes. Repeated old layouts have a
closed, monotone rational limit. This is not optimization of the old
layouts, arbitrary old 3/5/7 heights, or a solution of unrestricted #7.

Only Python's standard library is used. Checks remain active under -O.
Default replay binds the source probability and all certificate fields.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from hashlib import sha256
from math import isqrt
from pathlib import Path
import argparse
import json


HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-comb-sharpness-v1'
SOURCE = 'certificates/mod3_conditioned_geometry_certificate.json'
M = 315


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def digest(value):
    raw = json.dumps(encode(value), sort_keys=True, separators=(',', ':')).encode()
    return sha256(raw).hexdigest()


def crt(d, a, q, b):
    residue = a+d*((b-a)*pow(d, -1, q) % q)
    require(0 <= residue < d*q and residue % d == a % d
            and residue % q == b % q, 'literal CRT residue')
    return residue


def prefix(p, e, spoke):
    # Least significant digits: (p-2) repeated e-1 times, then spoke.
    return (p-2)*(p**(e-1)-1)//(p-1)+spoke*p**(e-1)


def kernel(alpha, delta):
    clipped = min(alpha, delta)
    g = 1/(1-clipped)
    h = clipped/(alpha*(1-clipped)) if alpha else F()
    beta = max(F(), alpha-delta)/(1-delta)
    require(g-h*alpha == 1 and 0 <= g-h and 0 <= beta <= 1,
            'normalized nonnegative distortion kernel')
    return g, h, beta


def layouts(divisors, H, forbidden_center, test_center, varying=False):
    nonunit = divisors[1:]
    forbidden = [{d: (forbidden_center+(e-1)*(i+1)+(e-1)**2) % d
                  if varying else forbidden_center % d
                  for i, d in enumerate(nonunit)} for e in range(1, H+1)]
    tests = [{d: (test_center+e*(i+2)+e*e) % d if varying else test_center % d
              for i, d in enumerate(divisors)} for e in range(H+1)]
    return forbidden, tests


def labels(old, divisors, p, H, forbidden, tests, variant='comb'):
    pure, mixed, test = [], [], []
    prefixes = []
    for e in range(1, H+1):
        q = p**e
        bp = 0 if variant == 'nested-pure' else prefix(p, e, 0)
        pure.append((q, bp))
        prefixes.append((e, bp))
        for j, d in enumerate(divisors[1:], 1):
            spoke = 1 if variant == 'duplicate-mixed' else 0 if variant == 'pure-mixed' else j
            b = prefix(p, e, spoke)
            mixed.append((d*q, crt(d, forbidden[e-1][d], q, b)))
            prefixes.append((e, b))
    for e in range(H+1):
        q = p**e
        for d in divisors:
            b = (1 if variant == 'bad-test' else 0 if variant == 'pure-test'
                 else 12 if variant == 'nonnested-test' and e == 2 else p-1)
            residue = tests[e][d] if e == 0 else crt(d, tests[e][d], q, b)
            test.append((d*q, residue))
    family = old+pure+mixed
    expected_moduli = {d*p**e for d in divisors for e in range(H+1)}-{1}
    require(len(family) == len(expected_moduli)
            and {d for d, a in family} == expected_moduli
            and len({d for d, a in family}) == len(family),
            'one actual original forbidden class per nonunit divisor')
    require({d for d, a in test} == expected_moduli | {1}
            and len(test) == len(expected_moduli)+1, 'complete original test labels')
    require(all(d > 1 and d % 2 and 0 <= a < d for d, a in family)
            and all(0 <= a < d for d, a in test), 'admissible odd CRT labels')
    return pure, mixed, test, prefixes, family


def symbolic_prefix_check(p, H, K, prefixes):
    require(K <= p-3 and len(prefixes) == (K+1)*H, 'distinct spokes and spare spine/root')
    powers = [p**e for e in range(H+1)]
    pairs = 0
    for i, (e, a) in enumerate(prefixes):
        require(a % p != p-1, 'entire test root is clean')
        for f, b in prefixes[:i]:
            require((a-b) % powers[min(e, f)] != 0, 'disjoint actual finite prefixes')
            pairs += 1
    require(pairs == len(prefixes)*(len(prefixes)-1)//2, 'all unordered prefix pairs checked')
    return pairs


def row_bounds(points, p, H, T, forbidden, tests):
    s = sum((F(1, p**e) for e in range(1, H+1)), F())
    lam, delta = 1-s, F(T-1, p-2)
    rows = []
    for x in points:
        loads = [sum(x % d == a for d, a in block.items()) for block in tests]
        counts = [sum(x % d == a for d, a in block.items()) for block in forbidden]
        bad_haar = sum((F(R, p**e) for e, R in enumerate(counts, 1)), F())
        alpha = bad_haar/lam
        g, h, beta = kernel(alpha, delta)
        c = g/lam
        running, energy = loads[0], F()
        for e, A in enumerate(loads[1:], 1):
            energy += F(A*A+2*A*running, p**e)
            running += A
        require(c == 1/max(lam-bad_haar, lam*(1-delta))
                and alpha < 1, 'exact comb cap and positive good mass')
        rows.append({'x': x, 'loads': loads, 'mixed_counts': counts,
                     'bad_haar': bad_haar, 'alpha': alpha, 'g': g, 'h': h,
                     'cap': c, 'charge': beta, 'pair_energy': energy,
                     'square': loads[0]**2+c*energy})
    return s, lam, rows


def means(rows, mu, f, W):
    square = sum((mu[r['x']]*r['square'] for r in rows), F())
    charge = sum((mu[r['x']]*r['charge'] for r in rows), F())
    return {'square': square, 'charge': charge, 'weighted_cost': f*square+W*charge}


def literal_check(old, divisors, points, mu, p, H, T, forbidden, tests, bounds, variant, f, W):
    """Independent residue tests and integer histograms, with no comb moment formula."""
    pure, mixed, test, _, family = labels(old, divisors, p, H, forbidden, tests, variant)
    q, delta = p**H, F(T-1, p-2)
    survivors = [y for y in range(q) if not any(y % d == a for d, a in pure)]
    require(survivors, 'literal pure survivors')
    lam = F(len(survivors), q)
    direct, excess_overlap = [], F()
    strict_square = strict_charge = 0
    for x, bound in zip(points, bounds):
        hist = [[0, 0, 0], [0, 0, 0]]  # count, squared load, square increment
        A0 = sum(x % d == a for d, a in tests[0].items())
        for y in survivors:
            z = crt(M, x, q, y)
            bad = int(any(z % d == a for d, a in mixed))
            require(not any(z % d == a for d, a in old+pure), 'literal old/pure support')
            L = sum(z % d == a for d, a in test)
            require(L >= A0, 'nonnegative positive-depth test increment')
            hist[bad][0] += 1
            hist[bad][1] += L*L
            hist[bad][2] += L*L-A0*A0
        alpha = F(hist[1][0], len(survivors))
        g, h, beta = kernel(alpha, delta)
        mass = (g*hist[0][0]+(g-h)*hist[1][0])/len(survivors)
        square = (g*hist[0][1]+(g-h)*hist[1][1])/len(survivors)
        charge = (g-h)*hist[1][0]/len(survivors)
        overlap = F(hist[1][2], len(survivors))
        require(mass == 1 and charge == beta, 'literal row normalization and assigned charge')
        require(lam >= 1-sum((F(1, p**e) for e in range(1, H+1)), F())
                and lam*alpha <= bound['bad_haar']
                and g/lam <= bound['cap'], 'alternate-prefix union and cap inequalities')
        require(square <= bound['square'] and charge <= bound['charge'],
                'alternate-prefix joint component bounds')
        strict_square += square < bound['square']
        strict_charge += charge < bound['charge']
        if variant == 'comb':
            require(square == bound['square'] and charge == bound['charge'] and overlap == 0,
                    'literal comb attains both bounds with zero extra overlap')
        direct.append({'x': x, 'square': square, 'charge': charge, 'alpha': alpha,
                       'mass': mass, 'increment_overlap': overlap})
        excess_overlap += mu[x]*overlap
    if variant in ('bad-test', 'pure-test', 'nonnested-test'):
        require(strict_charge == 0, 'test changes preserve actual assigned charge')
    if variant == 'pure-test':
        require(all(row['square'] == bound['loads'][0]**2 for row, bound in zip(direct, bounds)),
                'pure-deleted positive-depth tests leave exactly the old square')
    if variant == 'nonnested-test':
        require(H == 2 and all(bound['square']-row['square'] ==
                2*bound['cap']*bound['loads'][1]*bound['loads'][2]/p**2
                for row, bound in zip(direct, bounds)), 'exact loss from incompatible clean prefixes')
    return {'variant': variant, 'period': M*q, 'literal_supported_points': len(points)*len(survivors),
            'pure_survivor_haar_mass': lam, 'original_class_count': len(family),
            'strict_square_rows': strict_square, 'strict_charge_rows': strict_charge,
            'extra_square_bad_overlap': excess_overlap, 'row_values_sha256': digest(direct),
            **means(direct, mu, f, W)}


def repeated_limit(points, mu, divisors, p, T, forbidden_center, test_center, f, W):
    a, d = F(3*p-1, (p-1)**2), p-1-T
    rows = []
    for x in points:
        R = sum(x % q == forbidden_center % q for q in divisors[1:])
        A = sum(x % q == test_center % q for q in divisors)
        cap = F(p-1, p-1-min(1+R, T))
        charge = F(max(0, 1+R-T), d)
        rows.append({'x': x, 'R': R, 'A': A, 'cap': cap, 'charge': charge,
                     'square': A*A*(1+a*cap)})
    return a, rows, means(rows, mu, f, W)


def truncation_checks(points, mu, divisors, p, T, forbidden_center, test_center, f, W):
    """Coarse full-family tail bounds, checked on independently varying old blocks."""
    K, J = len(divisors)-1, len(divisors)**2
    lam_star, delta = F(p-2, p-1), F(T-1, p-2)
    c_star = 1/(lam_star*(1-delta))
    a = F(3*p-1, (p-1)**2)
    results = []
    for k, H in ((1, 2), (2, 8)):
        forbidden, tests = layouts(divisors, H, forbidden_center, test_center, True)
        _, _, full = row_bounds(points, p, H, T, forbidden, tests)
        _, _, cut = row_bounds(points, p, k, T, forbidden[:k], tests[:k+1])
        t = F(1, p**k*(p-1))
        epsilon = F(1, p**k)*(F(2*k+3, p-1)+F(2, (p-1)**2))
        cap_gap_bound = c_star*c_star*(K+1)*t
        charge_gap_bound = K*t/(lam_star*lam_star*(1-delta))
        square_gap_bound = J*(c_star*epsilon+cap_gap_bound*a)
        cost_gap_bound = f*square_gap_bound+W*charge_gap_bound
        for rh, rk in zip(full, cut):
            require(0 <= rh['pair_energy']-rk['pair_energy'] <= J*epsilon,
                    'all-family omitted pair-energy bound')
            require(0 <= rh['cap']-rk['cap'] <= cap_gap_bound
                    and 0 <= rh['charge']-rk['charge'] <= charge_gap_bound,
                    'all-family cap and charge truncation bounds')
            require(0 <= rh['square']-rk['square'] <= square_gap_bound,
                    'all-family square truncation bound')
        full_means, cut_means = means(full, mu, f, W), means(cut, mu, f, W)
        gap = full_means['weighted_cost']-cut_means['weighted_cost']
        require(0 <= gap <= cost_gap_bound, 'all-family nonnegative weighted truncation bound')
        results.append({'prime': p, 'cut_height': k, 'height': H, 'layout': 'varying-depth',
                        'J': J, 'lambda_star': lam_star, 'c_star': c_star,
                        'omitted_prefix_sum': t, 'omitted_pair_sum': epsilon,
                        'cap_gap_bound': cap_gap_bound, 'charge_gap_bound': charge_gap_bound,
                        'square_gap_bound': square_gap_bound, 'weighted_cost_gap_bound': cost_gap_bound,
                        'actual_weighted_cost_gap': gap,
                        'full_rows_sha256': digest(full), 'cut_rows_sha256': digest(cut)})
    return results


def evaluate(directory, params, expected_hashes=None):
    raw = read_artifact_bytes(directory/SOURCE)
    hashes = {SOURCE: sha256(raw).hexdigest()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'unchanged source certificate')
    source = json.loads(raw)
    require(source['schema'] == 'erdos7-mod3-conditioned-geometry-v1', 'source schema')
    cases = [c for c in source['cases'] if c['name'] == 'PG1']
    require(len(cases) == 1, 'unique PG1 case')
    case = cases[0]
    points, weights, den = case['points'], case['weight_numerators'], case['weight_denominator']
    old = [tuple(pair) for pair in case['family']]
    divisors = [d for d in range(1, M+1) if M % d == 0]
    K = len(divisors)-1
    require({d for d, a in old} == set(divisors[1:]) and len(old) == K == 11,
            'exact original low divisor inventory')
    require(points == [x for x in range(M) if not any(x % d == a for d, a in old)]
            and len(points) == len(weights) == 75 and den == 1000000007
            and all(type(w) is int and w > 0 for w in weights) and sum(weights) == den,
            'actual PG1 survivor probability')
    mu = {x: F(w, den) for x, w in zip(points, weights)}
    require(mu[2] == F(13119398, 1000000007), 'positive canonical witness row')
    T, f, W = params['threshold'], F(params['energy_weight']), F(params['charge_weight'])
    require(f >= 0 and W >= 0, 'nonnegative joint objective weights')
    heights = params['heights']
    require(heights == sorted(set(heights)) and heights[:2] == [1, 2]
            and all(type(h) is int and h > 0 for h in heights), 'finite heights include literal 1,2')
    require(params['primes'] == sorted(set(params['primes'])) and params['primes'], 'prime list')
    records, literal, limits, truncations = [], [], [], []
    literal_points = pair_checks = 0
    for p in params['primes']:
        require(type(p) is int and p > 2 and all(p % j for j in range(2, isqrt(p)+1))
                and M % p and K <= p-3 and 1 <= T < p-1,
                'coprime odd prime, spare spine/root, admissible threshold')
        truncations.extend(truncation_checks(points, mu, divisors, p, T,
                            params['forbidden_center'], params['test_center'], f, W))
        for mode, tc, varying in [('diagonal', params['forbidden_center'], False),
                                 ('off-diagonal', params['test_center'], False),
                                 ('varying-depth', params['test_center'], True)]:
            previous = None
            limit_rows = None
            if not varying:
                a_inf, limit_rows, limit_means = repeated_limit(
                    points, mu, divisors, p, T, params['forbidden_center'], tc, f, W)
                limits.append({'prime': p, 'layout': mode, 'a_infinity': a_inf,
                               'row_values_sha256': digest(limit_rows), **limit_means})
            for H in heights:
                if varying and H not in (1, 2):
                    continue
                forbidden, tests = layouts(divisors, H, params['forbidden_center'], tc, varying)
                pure, mixed, test, prefixes, family = labels(old, divisors, p, H, forbidden, tests)
                checked = symbolic_prefix_check(p, H, K, prefixes)
                pair_checks += checked
                s, lam, rows = row_bounds(points, p, H, T, forbidden, tests)
                require(s == F(p**H-1, (p-1)*p**H),
                        'exact finite geometric sum')
                a_H = sum((F(2*e+1, p**e) for e in range(1, H+1)), F())
                totals = means(rows, mu, f, W)
                record = {'prime': p, 'height': H, 'layout': mode, 'pure_forbidden_haar_mass': s,
                          'pure_survivor_haar_mass': lam, 'a_H': a_H,
                          'original_class_count': len(family), 'complete_test_count': len(test),
                          'disjoint_prefix_pairs_checked': checked, 'family_sha256': digest(family),
                          'test_sha256': digest(test), 'row_values_sha256': digest(rows), **totals}
                if not varying:
                    require(a_inf-a_H == F(1, p**H)*(F(2*H, p-1)+a_inf),
                            'complete exact geometric energy tail')
                    for row, lim in zip(rows, limit_rows):
                        A, R = lim['A'], lim['R']
                        require(row['loads'] == [A]*(H+1) and row['mixed_counts'] == [R]*H
                                and row['alpha'] == R*s/lam and row['pair_energy'] == A*A*a_H,
                                'repeated-layout specialization')
                        require(row['cap'] <= lim['cap'] and row['charge'] <= lim['charge']
                                and row['square'] <= lim['square'], 'exact rational limit upper values')
                    if previous is not None:
                        require(all(oldrow[key] <= row[key] for oldrow, row in zip(previous, rows)
                                    for key in ('alpha', 'cap', 'charge', 'square')),
                                'nondecreasing repeated-layout finite quantities')
                    previous = rows
                    record['limit_square_gap'] = limit_means['square']-totals['square']
                    record['limit_charge_gap'] = limit_means['charge']-totals['charge']
                    record['limit_weighted_cost_gap'] = limit_means['weighted_cost']-totals['weighted_cost']
                    witness = next(row for row in rows if row['x'] == 2)
                    record['witness_row'] = {key: witness[key] for key in ('alpha', 'cap', 'charge', 'square')}
                    if H == 1 and T == 8 and p in (17, 19) and params['forbidden_center'] == 2:
                        require(witness['charge'] == {17: F(53, 128), 19: F(61, 180)}[p],
                                'positive height-one charge floor')
                records.append(record)
                if H in (1, 2):
                    variants = (['comb', 'duplicate-mixed', 'pure-mixed', 'nested-pure', 'bad-test', 'pure-test']
                                +(['nonnested-test'] if H == 2 else [])) if mode == 'diagonal' else ['comb']
                    for variant in variants:
                        result = literal_check(old, divisors, points, mu, p, H, T, forbidden, tests, rows, variant, f, W)
                        if p in (17, 19) and T == 8 and params['forbidden_center'] == 2 and mode == 'diagonal':
                            if variant not in ('comb', 'nested-pure') or variant == 'nested-pure' and H == 2:
                                require(result['strict_square_rows'] > 0, 'default control has strict energy loss')
                            if variant in ('duplicate-mixed', 'pure-mixed') or variant == 'nested-pure' and H == 2:
                                require(result['strict_charge_rows'] > 0, 'default forbidden control has strict charge loss')
                            if variant == 'bad-test':
                                require(result['extra_square_bad_overlap'] > 0, 'default contaminated test has positive overlap')
                        literal_points += result['literal_supported_points']
                        literal.append({'prime': p, 'height': H, 'layout': mode, **result})
    return encode({'schema': SCHEMA, 'source_sha256': hashes, 'parameters': params,
                   'result': {'source_case': 'PG1', 'old_period': M, 'old_nonunit_divisors': divisors[1:],
                       'source_weight_denominator': den, 'records': records, 'repeated_layout_limits': limits,
                       'all_family_truncation_checks': truncations,
                       'literal_checks': literal, 'literal_point_evaluations': literal_points,
                       'disjoint_prefix_pair_checks': pair_checks,
                       'prefix_rule': 'Least significant digits: (p-2) repeated e-1 times, then spoke j; pure j=0, mixed j=1..11. Test prefix p-1 followed by zeros.',
                       'varying_layout_rule': 'For zero-based cofactor index i: forbidden residue (center+(e-1)*(i+1)+(e-1)^2) mod d; test residue (center+e*(i+2)+e^2) mod d.',
                       'scope': 'Fixed PG1 low law, old period315 and11 nonunit old cofactors. The finite-H ordinary theorem optimizes current-prime residues for any fixed old forbidden/test layouts at each depth; literal checks include independently varying depths. Closed monotone limits concern repeated old layouts only. Old-layout optimization, arbitrary old357 heights, later-prime iteration and unrestricted covering conclusions are not established.'}})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE/'certificates/pg1_comb_sharpness_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--primes', nargs='+', type=int, default=[17, 19])
    parser.add_argument('--heights', nargs='+', type=int, default=[1, 2, 4, 8, 16, 32, 64])
    parser.add_argument('--threshold', type=int, default=8)
    parser.add_argument('--forbidden-center', type=int, default=2)
    parser.add_argument('--test-center', type=int, default=47)
    parser.add_argument('--energy-weight', default='1')
    parser.add_argument('--charge-weight', default='270')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    params = {key: getattr(args, key) for key in ('primes', 'heights', 'threshold', 'forbidden_center',
                                               'test_center', 'energy_weight', 'charge_weight')}
    expected = None if args.write else json.loads(read_artifact_text(args.certificate))
    if expected is not None:
        require(expected['schema'] == SCHEMA and expected['parameters'] == params,
                'schema and explicitly selected parameters match certificate')
    actual = evaluate(args.source_directory, params, None if expected is None else expected['source_sha256'])
    if args.write:
        write_certificate_text(args.certificate, json.dumps(actual, indent=2)+'\n')
    else:
        require(actual == expected, 'complete deterministic comb certificate equality')
    print(json.dumps({'status': 'written' if args.write else 'verified',
                      'finite_records': len(actual['result']['records']),
                      'literal_checks': len(actual['result']['literal_checks']),
                      'literal_point_evaluations': actual['result']['literal_point_evaluations'],
                      'disjoint_prefix_pair_checks': actual['result']['disjoint_prefix_pair_checks']}))


if __name__ == '__main__':
    main()
