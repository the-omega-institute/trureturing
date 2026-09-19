#!/usr/bin/env python3
"""Reconstruct the actual-coefficient fixture and check all twelve low labels.

Default: recompute and compare the deterministic adjacent certificate.
--write: explicitly regenerate it. The auxiliary residues come from the
existing fixed-A certificate; all R/L loads and score entries are rebuilt from
the original PG1 probability law. This checks the C++ port on 32 spread A
loads against the original Python optimizer, not the older general DP suite.
"""

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
import argparse
import json
import time

HERE = Path(__file__).resolve().parent
_spec = spec_from_file_location('pg1_signed_score_oracle', HERE / 'pg1_signed_score_oracle.py')
oracle_module = module_from_spec(_spec)
_spec.loader.exec_module(oracle_module)
require = oracle_module.require


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=HERE / 'certificates/mod3_conditioned_geometry_certificate.json')
    parser.add_argument('--fixed-certificate', type=Path, default=HERE / 'certificates/exact_signed_digit_dp_certificate.json')
    parser.add_argument('--certificate', type=Path, default=HERE / 'certificates/pg1_all_low_scores_certificate.json')
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    started = time.monotonic()
    fixed_raw = read_artifact_bytes(args.fixed_certificate)
    fixed = json.loads(fixed_raw)
    require(sha256(read_artifact_bytes(args.source)).hexdigest() == fixed['source_sha256'],
            'existing fixed-A certificate binds the actual PG1 source')
    auxiliary = fixed['joint_auxiliary_example']
    require(auxiliary['depth'] == [1, 1, 1] and auxiliary['formula_description'] ==
            'E_mu[(4/3)*(B+R)^2+(149-B^2)*(L-4)_+/6]', 'the original actual-coefficient fixture')
    divisors = [(3**a * 5**b * 7**c, (1 + int(a == 2)) * (1 + b) * (1 + c))
                for a, b, c in product(range(3), range(2), range(2))]
    moment = auxiliary['moment_auxiliary_residues']
    charge = auxiliary['charge_auxiliary_residues']
    require(auxiliary['divisors'] == [d for d, _ in divisors] and
            len(moment) == len(charge) == len(divisors) and
            all(0 <= a < d and 0 <= b < d for (d, _), a, b in zip(divisors, moment, charge)),
            'one actual auxiliary residue per original divisor')
    with oracle_module.Oracle(args.source, args.binary) as oracle:
        case = oracle.case
        weights, den = case['weight_numerators'], case['weight_denominator']
        require(len(weights) == 75 and all(type(w) is int and w >= 0 for w in weights) and
                sum(weights) == den > 0, 'one exact probability law')
        point_scores = []
        point_loads = []
        for t, w in zip(oracle.points, weights):
            R = sum((mult - 1) * (t % d == a) for (d, mult), a in zip(divisors, moment))
            L = sum(mult * (t % d == b) for (d, mult), b in zip(divisors, charge))
            h = max(0, L - 4)
            point_scores.append([w * (8 * (k + R)**2 + (149 - k*k) * h) for k in range(13)])
            point_loads.append({'point': t, 'weight_numerator': w, 'R': R, 'L': L, 'h': h})
        require(point_loads == auxiliary['auxiliary_point_loads'], 'literal auxiliary load reconstruction')
        require(sum(row['h'] > 8 for row in point_loads) == 3, 'fixture includes negative quadratic curvature')
        A_fixed = tuple(sum(x % c == a for c, a in zip(oracle.dp.cofactors, fixed['fixed_old_residues']))
                        for x in oracle.xs)
        require(list(A_fixed) == fixed['fixed_old_load'], 'original fixed-A layout')
        fixed_index = next(i for i, (A, _) in enumerate(oracle.old) if A == A_fixed)
        check_indices = [i * (len(oracle.old) - 1) // 31 for i in range(32)]
        if fixed_index not in check_indices:
            check_indices[16] = fixed_index
        check_indices = sorted(set(check_indices))
        require(len(check_indices) == 32, '32 spread C++/Python comparisons including original A')
        scores = oracle.score_tensor({'point_scores': point_scores})
        result = oracle.optimize(scores, 6 * den, check_indices)
        solve_seconds = oracle.last_seconds
        fixed_comparison = next(row for row in result['python_comparisons'] if row['A_index'] == fixed_index)
        require(F(fixed_comparison['maximum_numerator'], 6 * den) == F(auxiliary['maximum']) and
                F(fixed_comparison['common_digit_maximum_numerator'], 6 * den) == F(auxiliary['common_digit_maximum']),
                'the previous fixed-A maxima are preserved exactly')
        require(F(result['maximum']) >= F(auxiliary['maximum']), 'all-A optimum includes original A')
    certificate = {'schema_version': 1,
                   'scope': 'one fixed auxiliary pair at depth (1,1,1), exactly maximized over all twelve original low labels; not all auxiliary profiles, arbitrary heights, or a final continuation bound',
                   'fixed_A_certificate_sha256': sha256(fixed_raw).hexdigest(),
                   'fixture_formula': auxiliary['formula_description'],
                   'negative_quadratic_point_count': 3,
                   'previous_fixed_A_maximum': auxiliary['maximum'],
                   'gain_over_previous_fixed_A': str(F(result['maximum']) - F(auxiliary['maximum'])),
                   'global_independent_vs_common_digit_gap': str(F(result['maximum']) - F(result['common_digit_maximum'])),
                   'result': result}
    if args.write:
        write_certificate_text(args.certificate, json.dumps(certificate, indent=2) + '\n')
    else:
        require(json.loads(read_artifact_text(args.certificate)) == certificate, 'deterministic certificate matches exact recomputation')
    print(json.dumps({'result': 'written' if args.write else 'verified',
                      'old_A_count': result['old_A_count'], 'python_comparison_count': 32,
                      'maximum': result['maximum'], 'common_digit_maximum': result['common_digit_maximum'],
                      'solve_seconds': solve_seconds, 'total_seconds': time.monotonic() - started}))


if __name__ == '__main__':
    main()
