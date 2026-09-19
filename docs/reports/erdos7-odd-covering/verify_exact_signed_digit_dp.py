#!/usr/bin/env python3
"""Brute-force and actual-PG1 checks for the signed CRT digit optimizer."""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2':
    raise ValueError('certificate IO source SHA-256 mismatch')
_certificate_sys.path.insert(0, str(_certificate_root))
from certificate_io import read_artifact_bytes, read_artifact_text, write_certificate_text
from fractions import Fraction as F
from hashlib import sha256
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from pathlib import Path
from random import Random
import argparse
import json

HERE = Path(__file__).resolve().parent
spec = spec_from_file_location('signed_dp', HERE / 'exact_signed_digit_dp.py')
dp = module_from_spec(spec)
spec.loader.exec_module(dp)
require = dp.require


def brute(oracle, A, scores):
    """Enumerate original residues, without old-cylinder deduplication or DP."""
    best = None
    for residues in product(*(range(oracle.q * c) for c in oracle.cofactors)):
        value = 0
        for y in range(oracle.q):
            for i, x in enumerate(oracle.points):
                point = x + oracle.m * (((y - x) * pow(oracle.m, -1, oracle.q)) % oracle.q)
                load = A[i] + sum(int(point % (oracle.q * c) == r)
                                  for c, r in zip(oracle.cofactors, residues))
                value += scores[y][i][load]
        if best is None or value > best:
            best = value
    return best


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source', type=Path,
                        default=HERE / 'certificates/mod3_conditioned_geometry_certificate.json')
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    rng = Random(20260917)
    checks = []
    for points, cofactors, q, m in [((0, 1, 4), (1, 3, 9), 2, 9),
                                  ((0, 1), (1, 3), 7, 3)]:
        oracle = dp.ExactSignedDigitDP(points, cofactors, q, m)
        for trial in range(6):
            A = [rng.randrange(3) for _ in points]
            scores = [[[F(rng.randrange(-15, 16), rng.randrange(1, 6))
                        for _ in range(max(A) + len(cofactors) + 1)]
                       for _ in points] for _ in range(q)]
            got = oracle.optimize(A, scores)
            expected = brute(oracle, A, scores)
            require(got['value'] == expected, 'independent original-residue brute force')
            checks.append({'old_points': list(points), 'cofactors': list(cofactors),
                           'digit_modulus': q, 'trial': trial, 'maximum': str(expected)})
    full = dp.ExactSignedDigitDP((0, 1, 2), (3,), 2, 3)
    negative = [[[-k for k in range(2)] for _ in range(3)] for _ in range(2)]
    f = full.optimize([0, 0, 0], negative)
    require(full.empty_singleton is None and f['value'] == -1,
            'full old carrier must pay negative singleton gain')
    proper = dp.ExactSignedDigitDP((0, 1), (3,), 2, 3)
    e = proper.optimize([0, 0], [[[-k for k in range(2)] for _ in range(2)]
                                for _ in range(2)])
    require(e['value'] == 0 and e['labels'][0]['old_residue'] == 2,
            'realizable empty singleton has zero gain')
    raw = read_artifact_bytes(args.source)
    case = next(c for c in json.loads(raw)['cases'] if c['name'] == 'PG1')
    points, xs = case['points'], case['old_points']
    nums, den = case['weight_numerators'], case['weight_denominator']
    require(points == [t for t in range(315)
                       if all(t % d != a for d, a in case['family'])], 'actual PG1 carrier')
    require(len(points) == len(nums) == 75 and len(xs) == 16 and
            all(type(w) is int and w >= 0 for w in nums) and sum(nums) == den > 0 and
            xs == sorted(set(t % 45 for t in points)),
            'PG1 dimensions and probability normalization')
    oracle = dp.ExactSignedDigitDP(xs)
    require([len(cy) for cy in oracle.cylinders] == [1, 3, 5, 6, 8, 17],
            'actual PG1 cylinder counts including empty')
    require(sum(map(len, oracle.states.values())) == 3024,
            'all old states after singleton elimination')
    old_loads = {tuple(sum(mask[i] for _, mask in choices) for i in range(len(xs)))
                 for choices in product(*oracle.cylinders)}
    A = [sum(int(x % c == 2 % c) for c in oracle.cofactors) for x in xs]
    def zeros():
        return [[[0] * 13 for _ in xs] for _ in range(7)]
    ri = {x: i for i, x in enumerate(xs)}
    # One actual row and two observed digits force independent digit choices.
    x = next(x for x in xs if sum(t % 45 == x for t in points) >= 2)
    pair = [(t, w) for t, w in zip(points, nums) if t % 45 == x][:2]
    counter = zeros()
    for t, w in pair:
        i, y = ri[x], t % 7
        counter[y][i] = [-w * (k - A[i] - 1) ** 2 for k in range(13)]
    c = oracle.optimize(A, counter)
    require(c['value'] == 0 and c['common_digit_value'] == -min(w for _, w in pair),
            'actual-carrier strict counterexample to common digit restriction')
    # Digit zero is a legal residue even though PG1 puts zero mass there.
    digit_zero = zeros()
    for t, w in zip(points, nums):
        i, y = ri[t % 45], t % 7
        digit_zero[y][i] = [-w * (k - A[i]) for k in range(13)]
    z = oracle.optimize(A, digit_zero)
    require(z['value'] == 0 and z['labels'][0]['digit'] == 0,
            'unobserved digit zero is required for signed scores')
    # A concrete fixed auxiliary pair from Nyx section 5 on the actual law.
    # Depth (1,1,1): R is higher-label moment load, L full charge load.
    # Scores = mu * [(4/3)*(B+R)^2 + (149-B^2)*(L-4)_+/6].
    divisors = [(3 ** a * 5 ** b * 7 ** c,
                 (1 + int(a == 2)) * (1 + b) * (1 + c))
                for a, b, c in product(range(3), range(2), range(2))]
    joint = zeros()
    aux = []
    moment_residues = [0, 2, 2, 12, 2, 2, 8, 59, 5, 38, 23, 32]
    charge_residues = [0, 6, 2, 27, 2, 20, 2, 62, 2, 20, 2, 272]
    require(len(divisors) == len(moment_residues) == len(charge_residues) and
            all(0 <= a < d and 0 <= b < d
                for (d, _), a, b in zip(divisors, moment_residues, charge_residues)),
            'one valid auxiliary residue for every original divisor')
    negative_quadratic_points = 0
    for t, w in zip(points, nums):
        R = sum((mult - 1) * int(t % d == a)
                for (d, mult), a in zip(divisors, moment_residues))
        L = sum(mult * int(t % d == b)
                for (d, mult), b in zip(divisors, charge_residues))
        h = max(0, L - 4)
        negative_quadratic_points += int(h > 8)
        i, y = ri[t % 45], t % 7
        # Multiply by 6*den to retain integral arithmetic.
        joint[y][i] = [w * (8 * (k + R) ** 2 + (149 - k * k) * h)
                       for k in range(13)]
        aux.append({'point': t, 'weight_numerator': w, 'R': R, 'L': L, 'h': h})
    j = oracle.optimize(A, joint)
    actual_replay = 0
    for t, w in zip(points, nums):
        B = A[ri[t % 45]] + sum(int(t % r['modulus'] == r['residue']) for r in j['labels'])
        actual_replay += joint[t % 7][ri[t % 45]][B]
    require(actual_replay == j['value'], 'original-modulus replay on all 75 actual points')
    require(negative_quadratic_points > 0, 'joint fixture exercises signed curvature')
    require(j['value'] > j['common_digit_value'],
            'actual-coefficient joint fixture needs independent digits')
    out = {'status': 'exact fixed-A optimizer and independent finite regression checks; no global-floor claim',
           'source_file': args.source.name, 'source_sha256': sha256(raw).hexdigest(),
           'source_law': 'PG1',
           'brute_force_checks': checks,
           'empty_singleton_maximum': e['value'], 'full_carrier_singleton_maximum': f['value'],
           'actual_old_cylinder_counts': c['cylinder_counts'],
           'old_states_without_singleton': c['old_states_without_singleton'],
           'old_residue_mask_combinations': 12240,
           'distinct_old_load_vectors': len(old_loads),
           'subset_transitions': c['subset_transitions'],
           'fixed_old_residues': [2 % d for d in oracle.cofactors], 'fixed_old_load': A,
           'common_digit_counterexample': {'points_and_weight_numerators': [list(tw) for tw in pair],
               'formula_description': '-mu(point)*(B-A-1)^2 on these two points; zero elsewhere',
               'maximum': str(F(c['value'], den)),
               'common_digit_maximum': str(F(c['common_digit_value'], den)), 'labels': c['labels']},
           'digit_zero_example': {'maximum': z['value'], 'labels': z['labels']},
           'joint_auxiliary_example': {'formula_description': 'E_mu[(4/3)*(B+R)^2+(149-B^2)*(L-4)_+/6]',
               'scope': 'one fixed-A, fixed-auxiliary, one-depth score profile; not the all-height or global final-floor maximum',
               'depth': [1, 1, 1], 'divisors': [d for d, _ in divisors],
               'moment_auxiliary_residues': moment_residues,
               'charge_auxiliary_residues': charge_residues,
               'negative_quadratic_points': negative_quadratic_points,
               'maximum': str(F(j['value'], 6 * den)),
               'common_digit_maximum': str(F(j['common_digit_value'], 6 * den)),
               'independent_digit_gain': str(F(j['value'] - j['common_digit_value'], 6 * den)),
               'labels': j['labels'], 'digit_partition': j['digit_partition'],
               'auxiliary_point_loads': aux}}
    destination = HERE / 'certificates/exact_signed_digit_dp_certificate.json'
    if args.write:
        write_certificate_text(destination, json.dumps(out, indent=2) + '\n')
    else:
        require(json.loads(read_artifact_text(destination)) == out,
                'stored certificate equals complete exact recomputation')
    print(json.dumps({'result': 'written' if args.write else 'verified',
                      'source_sha256': out['source_sha256'],
                      'brute_force_cases': len(checks),
                      'joint_maximum': out['joint_auxiliary_example']['maximum'],
                      'common_digit_maximum': out['joint_auxiliary_example']['common_digit_maximum'],
                      'independent_digit_gain': out['joint_auxiliary_example']['independent_digit_gain']}))


if __name__ == '__main__':
    main()
