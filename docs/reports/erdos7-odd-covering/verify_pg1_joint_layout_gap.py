#!/usr/bin/env python3
"""Refute identifying the repeated old forbidden and test layouts on PG1.

Keep the original PG1 law, p=17, T=8, f=59/45 and W=483.  For complete
old loads A,C define kappa(C)=16/(16-min(C,8)) and

    Phi(A,C) = E[f*(1+(25/128)*kappa(C))*A**2 + W*(C-8)_+/8].

The existing complete twelve-label oracle gives a directed rational upper
bound for max_B Phi(B,B); it includes all independent original residues,
not only coherent centers.  Coherent C at257 and A at47 exceed that bound
already at actual current-prime height3.  Every original CRT class, test,
and normalized kernel is independently replayed on the finite support.
The baseline f*A**2 is included throughout.

For ANY finite H with repeated diagonal old layout B, put
s_H=sum_{e=1}^H 17^-e and a_H=sum_{e=1}^H (2e+1)*17^-e.  Then
0<=s_H<=1/16, a_H<=25/128, and

 c_H = 1/max(1-B*s_H, (1-s_H)*8/15) <= kappa(B),
 beta_H = ((B-1)*s_H/(1-s_H)-7/15)_+/(8/15) <= (B-8)_+/8.

Both denominator branches decrease with s, while the unclipped charge
argument increases for B>=1.  Nonnegative weights give the finite-to-limit
bound for every height.  The exact omitted geometric and energy tails
are retained, as is the finite witness's complete gap to its own limit.

This refutes only the universal domination by ONE repeated diagonal layout.
It does not refute per-depth varying common layouts A_e=C_e, does not
optimize arbitrary higher 3/5/7 powers, and does not settle unrestricted #7.
No new optimizer or Lean theorem is introduced.  Checks survive Python -O.
Default execution recomputes the complete certificate; --write regenerates.
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
from pathlib import Path
import argparse
import json


HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-joint-layout-gap-v1'
SOURCE = 'certificates/mod3_conditioned_geometry_certificate.json'
P, T, H, M = 17, 8, 3, 315
FORBIDDEN_CENTER, TEST_CENTER = 257, 47
ENERGY_WEIGHT, CHARGE_WEIGHT = F(59, 45), F(483)
DELTA, A_INFINITY = F(7, 15), F(25, 128)
SCALE = 32768


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(key): encode(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(item) for item in value]
    return value


def load_module(name, filename):
    spec = spec_from_file_location(name, HERE/filename)
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def kappa(C):
    return F(P-1, P-1-min(C, T))


def limiting_cost(A, C):
    return (ENERGY_WEIGHT*(1+A_INFINITY*kappa(C))*A*A
            + CHARGE_WEIGHT*F(max(C-T, 0), P-1-T))


def evaluate(directory, expected_hashes=None):
    raw = read_artifact_bytes(directory/SOURCE)
    hashes = {SOURCE: sha256(raw).hexdigest()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'unchanged canonical PG1 source')
    source = json.loads(raw)
    require(source['schema'] == 'erdos7-mod3-conditioned-geometry-v1', 'source schema')
    cases = [case for case in source['cases'] if case['name'] == 'PG1']
    require(len(cases) == 1, 'unique actual PG1 law')
    case = cases[0]
    points, weights = case['points'], case['weight_numerators']
    denominator = case['weight_denominator']
    old = [tuple(pair) for pair in case['family']]
    divisors = [d for d in range(1, M+1) if M % d == 0]
    require(len(divisors) == 12 and len(old) == 11
            and {d for d, _ in old} == set(divisors[1:]), 'original old modulus inventory')
    require(points == [x for x in range(M) if not any(x % d == a for d, a in old)]
            and len(points) == len(weights) == 75 and denominator == 1000000007
            and all(type(w) is int and w > 0 for w in weights)
            and sum(weights) == denominator, 'unchanged survivor probability')
    mu = {x: F(w, denominator) for x, w in zip(points, weights)}

    # Round the WHOLE weighted rational upward, not its unweighted factor.
    scores = []
    for w in weights:
        row = []
        for B in range(13):
            exact = SCALE*w*limiting_cost(B, B)
            rounded = (exact.numerator+exact.denominator-1)//exact.denominator
            require(0 <= rounded-exact < 1, 'pointwise directed integer majorant')
            row.append(rounded)
        scores.append(row)
    oracle_module = load_module('pg1_gap_score_oracle', 'pg1_signed_score_oracle.py')
    with oracle_module.Oracle(directory/SOURCE) as oracle:
        require(oracle.source_sha256 == hashes[SOURCE] and oracle.points == points,
                'oracle uses the same physical PG1 law')
        diagonal = oracle.optimize(oracle.score_tensor({'point_scores': scores}),
                                   denominator=SCALE*denominator)
    diagonal_upper = F(diagonal['maximum'])
    diagonal_loads = diagonal['B_loads']
    diagonal_exact_witness = sum((mu[x]*limiting_cost(B, B)
                                 for x, B in zip(points, diagonal_loads)), F())
    rounding_error = F(len(points), SCALE*denominator)
    require(all(1 <= B <= 12 for B in diagonal_loads)
            and 0 <= diagonal_upper-diagonal_exact_witness < rounding_error,
            'full diagonal maximum lies between exact witness and directed upper')

    # Check the coefficients and endpoints used by the uniform-in-H proof
    # in the docstring.  This is algebra on all possible complete old loads,
    # not a search over a finite list of heights.
    s_infinity = F(1, P-1)
    a_formula = F(3*P-1, (P-1)**2)
    require(A_INFINITY == a_formula and DELTA == F(T-1, P-2)
            and 0 <= s_infinity < 1, 'exact infinite geometric and energy sums')
    monotone_rows = []
    for B in range(1, 13):
        first_endpoint = 1-B*s_infinity
        second_endpoint = (1-s_infinity)*(1-DELTA)
        alpha_endpoint = (B-1)*s_infinity/(1-s_infinity)
        beta_endpoint = max(F(), alpha_endpoint-DELTA)/(1-DELTA)
        require(B > 0 and 1-DELTA > 0 and B-1 >= 0
                and min(first_endpoint, second_endpoint) > 0
                and 1/max(first_endpoint, second_endpoint) == kappa(B)
                and beta_endpoint == F(max(B-T, 0), P-1-T),
                'decreasing positive cap denominators and increasing charge argument')
        monotone_rows.append({'B': B, 'first_denominator_decrease_rate': B,
                              'second_denominator_decrease_rate': 1-DELTA,
                              'alpha_derivative_numerator': B-1,
                              'first_denominator_endpoint': first_endpoint,
                              'second_denominator_endpoint': second_endpoint,
                              'limit_cap': kappa(B), 'limit_charge': beta_endpoint})

    comb = load_module('pg1_gap_comb', 'verify_pg1_comb_sharpness.py')
    forbidden, tests = comb.layouts(divisors, H, FORBIDDEN_CENTER, TEST_CENTER, False)
    pure, mixed, test, prefixes, family = comb.labels(old, divisors, P, H, forbidden, tests)
    pair_count = comb.symbolic_prefix_check(P, H, len(divisors)-1, prefixes)
    s, lam, bounds = comb.row_bounds(points, P, H, T, forbidden, tests)
    a_H = sum((F(2*e+1, P**e) for e in range(1, H+1)), F())
    s_tail = F(1, P**H*(P-1))
    a_tail = F(1, P**H)*(F(2*H, P-1)+A_INFINITY)
    require(s == F(P**H-1, (P-1)*P**H) and s_infinity-s == s_tail
            and A_INFINITY-a_H == a_tail, 'full exact omitted tails')
    finite_cost = limit_cost = F()
    witness_rows = []
    for x, row in zip(points, bounds):
        A = sum(x % d == TEST_CENTER % d for d in divisors)
        C = sum(x % d == FORBIDDEN_CENTER % d for d in divisors)
        cap = 1/max(1-C*s, (1-s)*(1-DELTA))
        beta = max(F(), (C-1)*s/(1-s)-DELTA)/(1-DELTA)
        finite_square = (1+a_H*cap)*A*A
        row_cost = ENERGY_WEIGHT*finite_square+CHARGE_WEIGHT*beta
        row_limit = limiting_cost(A, C)
        require(row['loads'] == [A]*(H+1) and row['mixed_counts'] == [C-1]*H
                and row['cap'] == cap and row['charge'] == beta
                and row['square'] == finite_square and row_cost <= row_limit,
                'independent repeated-layout formula agrees with comb row')
        finite_cost += mu[x]*row_cost
        limit_cost += mu[x]*row_limit
        witness_rows.append({'x': x, 'A': A, 'C': C, 'finite_cost': row_cost,
                             'limit_cost': row_limit})
    literal = comb.literal_check(old, divisors, points, mu, P, H, T,
                                 forbidden, tests, bounds, 'comb', ENERGY_WEIGHT, CHARGE_WEIGHT)
    require(len(family) == 47 and len(test) == 48 and M*P**H == 1547595
            and literal['literal_supported_points'] == 345450
            and literal['weighted_cost'] == finite_cost
            and literal['extra_square_bad_overlap'] == 0,
            'actual height-three47-class family and48-label test attain exact cost')
    require(finite_cost > diagonal_upper and limit_cost >= finite_cost,
            'finite off-diagonal actual family exceeds every repeated diagonal limit')

    return encode({'schema': SCHEMA, 'source_sha256': hashes,
        'parameters': {'old_period': M, 'prime': P, 'threshold': T, 'delta': DELTA,
                       'energy_weight': ENERGY_WEIGHT, 'charge_weight': CHARGE_WEIGHT,
                       'height': H, 'forbidden_center': FORBIDDEN_CENTER,
                       'test_center': TEST_CENTER, 'rounding_scale': SCALE},
        'result': {
            'scope': 'Refutes Phi(A,C)<=max_B Phi(B,B) for one complete old layout repeated at every current-prime depth. The diagonal maximum includes all independent twelve original old residues. No conclusion for independently varying common layouts A_e=C_e, higher old357 powers, later-prime iteration or unrestricted #7.',
            'objective': 'E_mu[(59/45)*(1+(25/128)*16/(16-min(C,8)))*A^2+(483/8)*(C-8)_+]; includes the old square baseline',
            'rounding_rule': 'ceil(scale*source_weight_numerator*point_cost)/(scale*source_weight_denominator)',
            'diagonal_oracle': diagonal,
            'diagonal_exact_winning_witness': diagonal_exact_witness,
            'diagonal_directed_upper': diagonal_upper,
            'strict_rounding_error_bound': rounding_error,
            'finite_to_limit': {'s_infinity': s_infinity, 'a_infinity': A_INFINITY,
                'all_height_reason': 'For 1<=B<=12, both positive cap denominator branches decrease with s, and alpha=(B-1)*s/(1-s) increases. Thus s_H<=s_infinity and a_H<=a_infinity imply f*(1+a_H*c_H)*B^2+W*beta_H<=Phi_point(B,B).',
                'load_endpoint_checks': monotone_rows},
            'off_diagonal': {'old_forbidden_layout': [[d, FORBIDDEN_CENTER % d] for d in divisors],
                'old_test_layout': [[d, TEST_CENTER % d] for d in divisors],
                'limit_cost': limit_cost, 'finite_cost': finite_cost,
                'finite_minus_diagonal_upper': finite_cost-diagonal_upper,
                'limit_minus_diagonal_upper': limit_cost-diagonal_upper,
                'complete_limit_minus_finite_gap': limit_cost-finite_cost,
                'omitted_prefix_sum': s_tail, 'omitted_pair_energy_sum': a_tail,
                'finite_prefix_sum': s, 'finite_pair_energy_sum': a_H,
                'pure_survivor_haar_mass': lam, 'period': M*P**H,
                'original_class_count': len(family), 'complete_test_count': len(test),
                'original_forbidden_family': family, 'complete_test_labels': test,
                'disjoint_prefix_pairs_checked': pair_count,
                'row_values_sha256': comb.digest(witness_rows), 'literal_check': literal}}})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=HERE/'certificates/pg1_joint_layout_gap_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(read_artifact_text(args.certificate))
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'certificate schema')
    actual = evaluate(args.source_directory, None if expected is None else expected['source_sha256'])
    if args.write:
        write_certificate_text(args.certificate, json.dumps(actual, indent=2)+'\n')
    else:
        require(actual == expected, 'complete deterministic joint-layout-gap certificate equality')
    result = actual['result']
    print(json.dumps({'status': 'written' if args.write else 'verified',
        'diagonal_directed_upper': result['diagonal_directed_upper'],
        'finite_off_diagonal_cost': result['off_diagonal']['finite_cost'],
        'strict_finite_gap': result['off_diagonal']['finite_minus_diagonal_upper'],
        'literal_point_evaluations': result['off_diagonal']['literal_check']['literal_supported_points']}))


if __name__ == '__main__':
    main()
