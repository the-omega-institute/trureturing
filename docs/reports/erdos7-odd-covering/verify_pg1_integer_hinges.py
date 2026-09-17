#!/usr/bin/env python3
"""Sharper integer hinges on the one fixed PG1 higher357 survivor law.

Compute the complete270-depth convex row bounds for thresholds3,7,8. Reuse
the hash-bound threshold4/6 arrays, and identify threshold5 with the existing
unweighted n1 whole cost without recomputing it. For thresholds3,4,6,7,8,
the complete original twelve-label oracle supplies the exact zero-depth
maximum separately for every fixed original3/original9 root pair.

If h(z) is the inherited convex row bound, h0 the exact zero-depth maximum,
and beta the finite-box probability, the new unconditional bound is

  U_new = U_old - (Pr(Z=0)+1-beta)*(h(0)-h0).

The outside anchor uses the same fixed original roots; its remaining
first-moment geometric coefficients are recomputed in full. No physical
height is truncated. All selected hinge floors at1+I3+I9 are zero, so
the nonnegative costs can be divided by the same independently positive
survival lower bound q0. One common survivor law works for every test and
every displayed threshold. This does not by itself close a later-prime
continuation or an unrestricted odd-covering problem.

New depth arrays are checked against independent full-layout enumeration
at the selected root/depth checkpoints. Every exact-zero rooted winner is
checked by the original Python digit DP and literal evaluation of all12
distinct original modulus labels at all75 actual points. Empty classes,
independent digit zero, and all original-label realizations are retained.

The older certificates are separately verified hash-bound prerequisites.
Default operation compares the entire deterministic certificate; --write
regenerates this extension only. Requires NumPy and a C++17 compiler.
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
from importlib.util import module_from_spec, spec_from_file_location
from itertools import product
from pathlib import Path
import argparse
import json
import numpy as np

HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-integer-hinges-v1'
SOURCES = ('certificates/mod3_conditioned_geometry_certificate.json',
           'certificates/original9_conditioned_geometry_certificate.json',
           'certificates/original9_convex_transfer_certificate.json', 'certificates/pg1_joint_tail_certificate.json')
IMPLEMENTATION = ('verify_point_geometry.py', 'verify_original9_convex_transfer.py',
                  'verify_pg1_exact_zero_depth.py', 'pg1_signed_score_oracle.py',
                  'pg1_signed_score_oracle.cpp', 'exact_signed_digit_dp.py')
NEW_THRESHOLDS = (3, 7, 8)
THRESHOLDS = (3, 4, 6, 7, 8)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def module(name, directory):
    spec = spec_from_file_location(name, directory/(name+'.py'))
    require(spec is not None and spec.loader is not None, 'adjacent canonical module')
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def evaluate(directory, expected_hashes=None):
    raw = {name: read_artifact_bytes(directory/name) for name in SOURCES+IMPLEMENTATION}
    hashes = {name: sha256(value).hexdigest() for name, value in raw.items()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'unchanged source certificates and oracle implementations')
    base, original, convex, joint = (json.loads(raw[name]) for name in SOURCES)
    require(base['schema'] == 'erdos7-mod3-conditioned-geometry-v1' and
            original['schema'] == 'erdos7-original9-conditioned-geometry-v1' and
            original['source_case'] == 'PG1' and original['source_sha256'] == hashes[SOURCES[0]],
            'canonical PG1 and original9 source')
    require(convex['schema'] == 'erdos7-original9-convex-transfer-v1' and
            convex['mod3_source_sha256'] == hashes[SOURCES[0]] and
            convex['original9_source_sha256'] == hashes[SOURCES[1]], 'same convex-transfer prerequisites')
    require(joint['schema'] == 'erdos7-pg1-joint-tail-v1' and
            all(joint['source_sha256'][name] == hashes[name] for name in SOURCES[:3]),
            'existing direct H5 whole-cost prerequisite chain')
    pg = module('verify_point_geometry', directory)
    cv = module('verify_original9_convex_transfer', directory)
    zero = module('verify_pg1_exact_zero_depth', directory)
    oracle_module = module('pg1_signed_score_oracle', directory)
    case = next(c for c in base['cases'] if c['name'] == 'PG1')
    points, old_points = case['points'], case['old_points']
    weights, den = case['weight_numerators'], case['weight_denominator']
    require(points == [x for x in range(315) if all(x % d != a for d, a in case['family'])] and
            len(points) == len(weights) == 75 and len(old_points) == 16 and
            all(type(w) is int and w >= 0 for w in weights) and sum(weights) == den == 1000000007,
            'one unchanged exact probability on the actual PG1 carrier')
    q0 = F(original['result']['survival_lower'])
    require(q0 == F(convex['result']['survival_lower']) > 0 and
            original['result']['hinge2']['H2_upper'] == '3', 'same actual higher357 law and survival bound')
    cut = (8, 5, 4)
    ds, gamma, _, _, depths, probabilities, beta, _ = pg.coeffs(cut)
    require(len(depths) == 270 and depths[0] == (0, 0, 0) and probabilities[0] == F(16, 35),
            'complete canonical auxiliary box and ordering')
    anchor = probabilities[0]+1-beta
    outside = []
    for d, g in zip(ds, gamma):
        inside = F(1)
        for p, h, limit in zip((3, 5, 7), (2, 1, 1), cut):
            e, quotient = 0, d
            while quotient % p == 0:
                e += 1
                quotient //= p
            inside *= sum((F(p-1, p**(z+1))*(1+z)**int(e == h)
                           for z in range(limit+1)), F(0))
        outside.append(g-inside+beta)
    require(min(outside) >= 0 and list(map(str, outside)) == convex['result']['outside_mean_coefficients'],
            'complete nonnegative first-moment geometric remainder')
    caps = [max(sum(w for x, w in zip(points, weights) if x % d == a) for a in range(d)) for d in ds]
    tail = sum((e*F(c, den) for e, c in zip(outside, caps)), F(0))
    require(str(tail) == convex['result']['outside_mean_increment'], 'unchanged complete outside increment')
    pts, xs, w = np.array(points, dtype=np.int64), np.array(old_points, dtype=np.int64), np.array(weights, dtype=np.int64)
    ri = np.array([old_points.index(x % 45) for x in points], dtype=np.int64)
    R = np.array([int(w[ri == i].sum()) for i in range(16)], dtype=np.int64)
    v = np.array([int(w[ri == i].max()) for i in range(16)], dtype=np.int64)
    require(np.all(R >= v), 'nonnegative convex row-relaxation weights')
    mods = (3, 5, 9, 15)
    choices = list(product(*(sorted(set(map(int, xs % d))) for d in mods)))
    feat = np.array([[[int(x % d == a) for x in xs] for d, a in zip(mods, row)] for row in choices], dtype=np.int64)
    roots = np.array([r[0] for r in choices], dtype=np.int64)
    _, full_feat = pg.geometry(xs)
    full_roots = np.array([int(xs[np.flatnonzero(row[1])[0]] % 3) for row in full_feat], dtype=np.int64)
    require(len(feat) == 280 and len(full_feat) == 4480, 'complete original convex layout domains')
    safety = 4*den*(6*78)**2
    require(safety < 2**63, 'all full-box convex singleton intermediates fit signed64')
    cache = {}
    for a, b in product(range(9), range(6)):
        B = 1+np.einsum('aer,e->ar', feat, np.array([1, 1+b, 1+a, 1+b], dtype=np.int64))
        FB = np.einsum('aer,e->ar', full_feat, np.array([1, 1, 1+b, 1+a, 1+b, (1+a)*(1+b)], dtype=np.int64))
        cache[a, b] = B, FB
    root_pairs = [(i, j) for j in sorted(set(map(int, xs % 9))) for i in (1, 2)]
    require(len(root_pairs) == 10, 'all ten original3/original9 root pairs')
    tables = {key: {} for key in root_pairs}
    inherited = {(r['root3'], r['root9']): r for r in convex['result']['branches']}
    require(set(inherited) == set(root_pairs) and len(convex['result']['branches']) == 10,
            'complete inherited original-root branches')
    for key in root_pairs:
        for t in (4, 6):
            values = inherited[key]['hinges'][str(t)]['numerators']
            require(len(values) == 270 and all(type(n) is int and n >= 0 for n in values),
                    'complete inherited H4/H6 observations')
            tables[key][t] = list(values)
    checkpoints = {(1, (0, 0, 0), 3, 1), (7, (0, 0, 0), 7, 1),
                   (8, (0, 0, 0), 8, 2), (1, (0, 0, 1), 3, 1)}
    checks = []
    query_count = 0
    for j in sorted(set(map(int, xs % 9))):
        for i in (1, 2):
            for t in NEW_THRESHOLDS:
                tables[i, j][t] = []
        for z in depths:
            B, FB = cache[z[:2]]
            A = B-feat[:, 2, :]+(xs % 9 == j)
            FA = FB-full_feat[:, 3, :]+(xs % 9 == j)
            for t in NEW_THRESHOLDS:
                got = cv.costs(A, B, FA, FB, R, v, roots, full_roots, z, t)
                query_count += 1
                for i in (1, 2):
                    tables[i, j][t].append(got[str(i)])
                    if (j, z, t, i) in checkpoints:
                        direct = cv.direct(FA, FB, R, v, full_roots, z, t, i)
                        require(direct == got[str(i)], 'independent complete4480-layout-pair hinge check')
                        checks.append({'root3': i, 'root9': j, 'depth': list(z), 'threshold': t, 'numerator': direct})
    require(query_count == 4050 and len(checks) == len(checkpoints), 'complete requested new-depth query domain')
    records = {key: {'root3': key[0], 'root9': key[1], 'hinges': {}} for key in root_pairs}
    score_checks = []
    with oracle_module.Oracle(directory/SOURCES[0]) as oracle:
        require(oracle.points == points and oracle.xs == old_points and oracle.source_sha256 == hashes[SOURCES[0]],
                'same actual carrier in the exact twelve-label oracle')
        old_index = {A: i for i, (A, _) in enumerate(oracle.old)}
        root_layouts = {key: {} for key in root_pairs}
        # One deduplicated A can have several original-root realizations.
        # Enumerate every realization before applying the root restriction.
        for choice in product(*oracle.dp.cylinders):
            key = (choice[1][0], choice[3][0])
            if key in root_layouts:
                A = tuple(sum(mask[i] for _, mask in choice) for i in range(16))
                root_layouts[key].setdefault(old_index[A], tuple(a for a, _ in choice))
        for t in THRESHOLDS:
            tensor = oracle.score_tensor({'point_scores': [[weight*max(k-t, 0) for k in range(13)] for weight in weights]})
            values, score_bound, score_hash = zero.all_old_values(oracle, tensor)
            replay_cache = {}
            for key in root_pairs:
                layouts = root_layouts[key]
                require(layouts, 'nonempty complete original-root exact domain')
                idx, exact, _ = max((values[i] for i in layouts), key=lambda r: r[1])
                common_idx, _, common = max((values[i] for i in layouts), key=lambda r: r[2])
                for at in {idx, common_idx}:
                    if at not in replay_cache:
                        replay_cache[at] = oracle.dp.optimize(oracle.old[at][0], tensor)
                    replay = replay_cache[at]
                    require((replay['value'], replay['common_digit_value']) == values[at][1:],
                            'original Python DP verifies both exact rooted winners')
                labels = [{'modulus': d, 'residue': a} for d, a in zip(oracle.dp.cofactors, layouts[idx])]
                labels += [{'modulus': r['modulus'], 'residue': r['residue']} for r in replay_cache[idx]['labels']]
                family = {r['modulus']: r['residue'] for r in labels}
                require(len(labels) == len(family) == 12 and set(family) == set(ds) and
                        family[3] == key[0] and family[9] == key[1], 'all original labels and fixed roots retained')
                loads = [sum(x % r['modulus'] == r['residue'] for r in labels) for x in points]
                require(sum(weight*max(load-t, 0) for weight, load in zip(weights, loads)) == exact,
                        'literal original twelve-label hinge on all75 actual points')
                nn = tables[key][t]
                require(len(nn) == 270 and all(type(n) is int and n >= 0 for n in nn) and exact <= nn[0],
                        'complete nonnegative bounds and valid exact-zero improvement')
                old_U = (1-beta)*F(nn[0], den)+sum((p*F(n, den) for p, n in zip(probabilities, nn)), F(0))+tail
                if t in (4, 6):
                    source_row = inherited[key]['hinges'][str(t)]
                    require(old_U == F(source_row['lambda_upper']) and old_U/q0 == F(source_row['nu_upper']),
                            'complete H4/H6 inherited arrays and tails reconstructed')
                saving = anchor*F(nn[0]-exact, den)
                new_U = old_U-saving
                require(new_U >= 0, 'nonnegative complete unconditional hinge bound')
                row = {'old_lambda_upper': str(old_U), 'old_zero_depth_upper_numerator': nn[0],
                       'exact_zero_depth_numerator': exact, 'exact_common_digit_numerator': common,
                       'unconditional_saving': str(saving), 'lambda_upper': str(new_U), 'nu_upper': str(new_U/q0),
                       'other269_depths_sha256': digest(nn[1:]), 'admissible_distinct_A': len(layouts),
                       'root_A_indices_sha256': digest(sorted(layouts)), 'maximizing_A_index': idx,
                       'original_labels': labels}
                if t in NEW_THRESHOLDS:
                    row['depth_upper_numerators'] = [exact]+nn[1:]
                else:
                    row['inherited_depth_source'] = SOURCES[2]
                    row['inherited_depth_numerators_sha256'] = digest(nn)
                records[key]['hinges'][str(t)] = row
            score_checks.append({'threshold': t, 'score_sha256': score_hash, 'score_abs_bound': score_bound})
        domain_hash = oracle.domain_sha256
    ordered = [records[key] for key in root_pairs]
    bounds = {str(t): max(F(r['hinges'][str(t)]['nu_upper']) for r in ordered) for t in THRESHOLDS}
    old_h4, old_h6 = F(convex['result']['H4_upper']), F(convex['result']['H6_upper'])
    prior = {'3': (3+old_h4)/2, '4': old_h4, '6': old_h6, '7': old_h6, '8': old_h6}
    require(all(bounds[str(t)] < prior[str(t)] for t in THRESHOLDS), 'five strict simultaneous hinge improvements')
    whole = joint['result']['unweighted_whole_cost']
    whole_roots = {(r['charge_root3'], r['charge_root9']) for r in whole['records']}
    require(len(whole['records']) == 10 and whole_roots == set(root_pairs), 'existing direct H5 covers every root')
    H5 = max(F(r['costs']['n1']['lambda_upper']) for r in whole['records'])/q0
    require(H5 == F(whole['lambda_upper']['1'])/q0, 'reuse the existing complete direct H5 observation')
    return {'schema': SCHEMA, 'source_sha256': hashes,
            'result': {'depth_box': list(cut), 'new_depth_thresholds': list(NEW_THRESHOLDS),
                'inherited_depth_thresholds': [4, 6], 'exact_zero_thresholds': list(THRESHOLDS),
                'source_survival_lower': str(q0), 'weight_denominator': den,
                'zero_depth_probability': str(probabilities[0]), 'outside_probability': str(1-beta),
                'zero_anchor_coefficient': str(anchor), 'tail_divisors': ds,
                'complete_outside_mean_coefficients': list(map(str, outside)), 'cap_numerators': caps,
                'complete_outside_mean_increment': str(tail), 'records': ordered,
                'conditional_hinge_upper_bounds': {k: str(v) for k, v in bounds.items()},
                'prior_hinge_upper_bounds': {k: str(v) for k, v in prior.items()},
                'improvements': {k: str(prior[k]-v) for k, v in bounds.items()},
                'worst_roots': {str(t): [r['root3'], r['root9']] for t in THRESHOLDS
                                for r in [max(ordered, key=lambda row: F(row['hinges'][str(t)]['nu_upper']))]},
                'reused_H5': {'source': SOURCES[3], 'field': 'result.unweighted_whole_cost.records.costs.n1',
                              'conditional_upper': str(H5), 'scope': 'Existing complete observation; not newly computed.'},
                'direct_full_layout_checks': checks, 'new_convex_query_count': query_count,
                'maximum_convex_integer_bound': safety, 'oracle_domain_sha256': domain_hash,
                'exact_zero_score_checks': score_checks,
                'scope': 'One unchanged PG1 low probability and actual higher357 survivor law. All10 fixed original3/original9 roots, complete270-depth observations with exact000 and outside anchor, and complete first-moment tails. Arbitrary finite physical heights. Five simultaneous integer hinge improvements; no later-prime consumer or unrestricted covering conclusion.'}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE/'certificates/pg1_integer_hinges_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(read_artifact_text(args.certificate))
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'integer-hinge extension schema')
    actual = evaluate(args.source_directory, None if expected is None else expected['source_sha256'])
    if args.write:
        write_certificate_text(args.certificate, json.dumps(actual, indent=2)+'\n')
    else:
        require(actual == expected, 'complete deterministic integer-hinge certificate equality')
    print(json.dumps({'status': 'written' if args.write else 'verified',
                      'conditional_hinge_upper_bounds': actual['result']['conditional_hinge_upper_bounds'],
                      'worst_roots': actual['result']['worst_roots']}))


if __name__ == '__main__':
    main()
