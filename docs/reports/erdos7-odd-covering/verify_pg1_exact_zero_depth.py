#!/usr/bin/env python3
"""Exact PG1 zero-depth square maxima with original mod3/mod9 roots retained.

Reuse the canonical complete twelve-label oracle, with all old loads and
independent seven digits. Replace only the zero-depth square and the matching
outside-box anchor in the hash-bound original9 certificate. The other269
depth upper bounds are inherited; complete geometric tail coefficients are
recomputed. No auxiliary profile is sampled and no higher-depth search runs.
Default: compare the deterministic certificate. --write explicitly writes it.
Requires NumPy and an available C++17 compiler, as does the canonical oracle.
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
from tempfile import TemporaryDirectory
import argparse
import json
import subprocess

HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-exact-zero-depth-v1'
SOURCES = ('certificates/mod3_conditioned_geometry_certificate.json',
           'certificates/original9_conditioned_geometry_certificate.json',
           'certificates/pg1_signed_g2_certificate.json', 'certificates/pg1_joint_tail_certificate.json')


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def module(name, directory):
    spec = spec_from_file_location(name, directory / (name + '.py'))
    require(spec is not None and spec.loader is not None, 'canonical module loader')
    result = module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def all_old_values(oracle, tensor):
    """Read the canonical C++ oracle's complete temporary all-A output.

    The canonical public summary only returns the unrestricted winner.
    Root restrictions need the complete table, so retain it in memory here
    while preserving the driver's exact input and integer-range contract.
    """
    require(len(tensor) == 7 and all(len(plane) == 16 for plane in tensor), 'score dimensions')
    require(all(len(row) == 13 and all(type(v) is int for v in row)
                for plane in tensor for row in plane), 'integer load-score tables')
    require(all(not any(tensor[y][i]) for y in range(7) for i in range(16)
                if (y, i) not in oracle.present), 'zero scores at absent physical points')
    bound = sum(max(map(abs, row)) for plane in tensor for row in plane)
    require(4*bound < 2**61, 'canonical signed-score int64 guard')
    score_text = ''.join(' '.join(map(str, row)) + '\n' for plane in tensor for row in plane)
    text = f'{len(oracle.old)} {oracle.state_count}\n' + score_text + oracle.domain
    with TemporaryDirectory(prefix='pg1-exact-zero-') as temporary:
        input_path = Path(temporary) / 'input.txt'
        output_path = Path(temporary) / 'values.txt'
        write_certificate_text(input_path, text)
        run = subprocess.run([str(oracle.binary), str(input_path), str(output_path)],
                             check=True, capture_output=True, text=True)
        summary = json.loads(run.stdout)
        values = [tuple(map(int, line.split())) for line in read_artifact_text(output_path).splitlines()]
    require(len(values) == 11808 and all(len(row) == 3 for row in values)
            and [row[0] for row in values] == list(range(11808)), 'complete ordered all-A table')
    winner = max(values, key=lambda row: row[1])
    require(summary['queries'] == len(values) and summary['maximum_numerator'] == winner[1]
            and summary['maximizing_A_index'] == winner[0], 'canonical C++ summary equality')
    return values, bound, sha256(score_text.encode()).hexdigest()


def evaluate(directory, expected_hashes=None):
    raw = {name: read_artifact_bytes(directory / name) for name in SOURCES}
    hashes = {name: sha256(value).hexdigest() for name, value in raw.items()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'hash-bound source certificates')
    source = json.loads(raw[SOURCES[1]])
    require(source['schema'] == 'erdos7-original9-conditioned-geometry-v1'
            and source['source_sha256'] == hashes[SOURCES[0]]
            and source['source_case'] == 'PG1' and source['reference_target'] == '33',
            'unchanged PG1 source and original9 criterion')
    oracle_module = module('pg1_signed_score_oracle', directory)
    pg = module('verify_point_geometry', directory)
    cut = (8, 5, 4)
    ds, _, _, _, depths, probabilities, beta, outside = pg.coeffs(cut)
    require(len(depths) == 270 and depths[0] == (0, 0, 0)
            and probabilities[0] == F(16, 35) and min(outside) >= 0,
            'canonical depth order and complete nonnegative geometric tail')
    anchor = probabilities[0] + 1-beta
    records = []
    with oracle_module.Oracle(directory / SOURCES[0]) as oracle:
        case = oracle.case
        weights, den = case['weight_numerators'], case['weight_denominator']
        require(oracle.source_sha256 == hashes[SOURCES[0]]
                and all(type(w) is int and w >= 0 for w in weights)
                and sum(weights) == den == 1000000007, 'fixed exact PG1 probability')
        caps = [max(sum(w for x, w in zip(oracle.points, weights) if x % d == a)
                    for a in range(d)) for d in ds]
        require(caps == source['result']['cap_numerators'], 'same full-tail cylinder observations')
        tail = sum((coefficient*F(value, den) for coefficient, value in zip(outside, caps)), F(0))
        tensor = oracle.score_tensor({'point_scores': [[w*k*k for k in range(13)] for w in weights]})
        values, score_bound, score_hash = all_old_values(oracle, tensor)
        old_index = {A: i for i, (A, _) in enumerate(oracle.old)}
        root_pairs = {(i, j) for i in (1, 2) for j in sorted({x % 9 for x in oracle.xs})}
        root_layouts = {key: {} for key in root_pairs}
        # A load can have different original-label realizations. Re-enumerate
        # those realizations before filtering roots; the oracle's single
        # representative for a deduplicated A is not sufficient for this step.
        for choices in product(*oracle.dp.cylinders):
            key = (choices[1][0], choices[3][0])
            if key in root_layouts:
                A = tuple(sum(mask[i] for _, mask in choices) for i in range(16))
                root_layouts[key].setdefault(old_index[A], tuple(a for a, _ in choices))
        old_records = source['result']['records']
        require(len(old_records) == len(root_pairs) == 10
                and {(r['root3'], r['root9']) for r in old_records} == root_pairs,
                'all ten original3/original9 branches with no duplicate or missing root')
        for old in old_records:
            key = (old['root3'], old['root9'])
            layouts = root_layouts[key]
            require(layouts, 'nonempty original-root layout domain')
            idx, exact, common_here = max((values[i] for i in layouts), key=lambda row: row[1])
            common_idx, _, common = max((values[i] for i in layouts), key=lambda row: row[2])
            for check in {idx, common_idx}:
                replay = oracle.dp.optimize(oracle.old[check][0], tensor)
                require((replay['value'], replay['common_digit_value']) == values[check][1:],
                        'independent Python DP agrees on both rooted winners')
            replay = oracle.dp.optimize(oracle.old[idx][0], tensor)
            labels = [{'modulus': d, 'residue': a} for d, a in zip(oracle.dp.cofactors, layouts[idx])]
            labels += [{'modulus': r['modulus'], 'residue': r['residue']} for r in replay['labels']]
            family = {r['modulus']: r['residue'] for r in labels}
            require(len(labels) == len(family) == 12 and set(family) == set(ds)
                    and family[3] == key[0] and family[9] == key[1], 'unchanged original labels and roots')
            loads = [sum(x % r['modulus'] == r['residue'] for r in labels) for x in oracle.points]
            require(sum(w*b*b for w, b in zip(weights, loads)) == exact,
                    'literal twelve-label square witness on all75 points')
            pure, fixed = old['pure7_numerators'], old['fixedA_numerators']
            require(len(pure) == len(fixed) == 270
                    and all(type(v) is int and v >= 0 for v in pure + fixed),
                    'complete inherited inside-box upper bounds')
            inherited = list(map(min, zip(pure, fixed)))
            require(exact <= inherited[0], 'exact zero-depth maximum dominates old relaxation')
            old_U = ((1-beta)*F(inherited[0], den)
                     + sum((p*F(n, den) for p, n in zip(probabilities, inherited)), F(0)) + tail)
            require(old_U == F(old['U']), 'old U reconstructed with complete unchanged tail')
            saving = anchor * F(inherited[0]-exact, den)
            new_U = old_U-saving
            excess = new_U+F(old['weighted_deletion_upper'])-33
            records.append({'root3': key[0], 'root9': key[1],
                            'admissible_distinct_A': len(layouts),
                            'root_A_indices_sha256': digest(sorted(layouts)),
                            'old_zero_depth_upper_numerator': inherited[0],
                            'exact_zero_depth_numerator': exact,
                            'exact_common_digit_numerator': common,
                            'other269_depth_upper_bounds_sha256': digest(inherited[1:]),
                            'unconditional_saving': str(saving), 'new_U': str(new_U),
                            'inherited_weighted_deletion_upper': old['weighted_deletion_upper'],
                            'new_signed_excess': str(excess), 'maximizing_A_index': idx,
                            'original_labels': labels})
        require(max(row['exact_zero_depth_numerator'] for row in records)
                == max(row[1] for row in values), 'root domains cover the unrestricted positive-square maximum')
        domain_hash = oracle.domain_sha256
    q0 = F(source['result']['survival_lower'])
    require(q0 > 0, 'unchanged independent same-law survival')
    worst = max(records, key=lambda row: F(row['new_signed_excess']))
    excess = max(F(0), F(worst['new_signed_excess']))
    new_G = 33+excess/q0
    require(new_G < F(source['result']['Gamma_upper']), 'strict uniform same-law source improvement')
    signed = json.loads(raw[SOURCES[2]])
    joint = json.loads(raw[SOURCES[3]])
    require(signed['schema'] == 'erdos7-pg1-signed-g2-v1'
            and joint['schema'] == 'erdos7-pg1-joint-tail-v1'
            and signed['source_joint_sha256'] == signed['result']['source_joint_sha256'] == hashes[SOURCES[3]]
            and signed['result']['original_source_sha256'] == joint['source_sha256']
            and all(joint['source_sha256'][name] == hashes[name] for name in SOURCES[:2])
            and F(signed['result']['source_survival_lower']) == q0,
            'same-law signed-G2 and joint-tail prerequisite chain')
    final_survival = F(joint['result']['independent_tail_survival_lower'])
    require(final_survival > 0 and F(joint['floor_reference']) == 149,
            'inherited independent final survival and final reference')
    old_excesses = {(r['root3'], r['root9']): F(r['criterion_excess'])
                   for r in source['result']['records']}
    new_excesses = {(r['root3'], r['root9']): F(r['new_signed_excess']) for r in records}
    old_maximum, new_maximum = max(old_excesses.values()), max(new_excesses.values())
    P, M = F(1403, 630), F(4, 3)
    consumer_rows = []
    signed_rows = signed['result']['records']
    require(len(signed_rows) == 10
            and {(r['final_root3'], r['final_root9']) for r in signed_rows} == set(old_excesses),
            'all ten final-root consumers retained')
    for row in signed_rows:
        key = (row['final_root3'], row['final_root9'])
        reduction = (P-M)*(old_maximum-new_maximum) + M*(old_excesses[key]-new_excesses[key])
        require(reduction >= 0, 'nonnegative complete square-criterion improvement')
        candidates = {}
        old_candidates = []
        for prefix in ('prior', 'signed', 'inherited'):
            A, B = F(row[prefix+'_criterion_constant']), F(row[prefix+'_criterion_inverse_Q'])
            old_value = A+B/q0
            require(B > 0 and old_value == F(row[prefix+'_criterion_excess']),
                    'inherited complete common-Q criterion')
            new_B = B-reduction
            require(new_B > 0, 'improved complete candidate still maximized at Q=q0')
            candidates[prefix] = {'constant': str(A), 'inverse_Q': str(new_B),
                                  'criterion_excess': str(A+new_B/q0)}
            old_candidates.append(old_value)
        require(min(old_candidates) == F(row['criterion_excess']), 'old complete-candidate selection')
        selected = min(candidates, key=lambda name: F(candidates[name]['criterion_excess']))
        consumer_rows.append({'final_root3': key[0], 'final_root9': key[1],
                              'inverse_Q_reduction': str(reduction), 'candidates': candidates,
                              'selected_complete_criterion': selected,
                              'criterion_excess': candidates[selected]['criterion_excess']})
    final_worst = max(consumer_rows, key=lambda row: F(row['criterion_excess']))
    final_excess = F(final_worst['criterion_excess'])
    final_bound = 149+final_excess
    require(final_excess < 0 and final_bound < F(signed['result']['Gamma13_upper']),
            'negative final excess yields stronger Gamma13 with actual final mass at most one')
    loss_limit = q0*(35-new_G)/34
    require(0 < loss_limit < q0, 'positive target35 conditioning tolerance')
    loss_numerator = loss_limit*den
    result = {'depth_box': list(cut), 'exact_depth': [0, 0, 0],
              'exact_depth_probability': str(probabilities[0]), 'outside_probability': str(1-beta),
              'zero_anchor_coefficient': str(anchor), 'tail_divisors': ds,
              'complete_outside_square_coefficients': list(map(str, outside)),
              'complete_outside_square_increment': str(tail),
              'oracle_domain_sha256': domain_hash, 'score_sha256': score_hash,
              'score_abs_bound': score_bound, 'records': records,
              'source_survival_lower': str(q0), 'old_Gamma_upper': source['result']['Gamma_upper'],
              'maximum_nonnegative_excess': str(excess), 'Gamma_upper': str(new_G),
              'improvement': str(F(source['result']['Gamma_upper'])-new_G),
              'worst_roots': [worst['root3'], worst['root9']],
              'fixed11_13_consumer': {'source_multiplier_first_moment': str(M),
                  'source_multiplier_second_moment': str(P),
                  'inherited_independent_final_survival_lower': str(final_survival),
                  'records': consumer_rows, 'maximum_criterion_excess': str(final_excess),
                  'old_Gamma13_upper': signed['result']['Gamma13_upper'], 'Gamma13_upper': str(final_bound),
                  'worst_roots': [final_worst['final_root3'], final_worst['final_root9']]},
              'target35_conditioning': {'loss_limit': str(loss_limit), 'weight_denominator': den,
                  'integer_loss_limit': loss_numerator.numerator // loss_numerator.denominator,
                  'scope': 'Threshold only; no new carrier matching or coverage count is claimed.'},
              'scope': 'Same actual PG1 probability and higher357 survival event; arbitrary finite physical heights and all original test residues. Exact zero auxiliary depth and exact outside-box anchor; other269 inside-box bounds and full geometric tails retained. The fixed11/13 consumer retains all previously certified physical kernels and tails. No new carrier count or unrestricted-prime resolution is asserted.'}
    return {'schema': SCHEMA, 'source_sha256': hashes, 'result': result}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=HERE / 'certificates/pg1_exact_zero_depth_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(read_artifact_text(args.certificate))
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'certificate schema')
    actual = evaluate(args.source_directory, None if expected is None else expected['source_sha256'])
    if args.write:
        write_certificate_text(args.certificate, json.dumps(actual, indent=2) + '\n')
    else:
        require(actual == expected, 'complete exact zero-depth certificate')
    print(json.dumps({key: actual['result'][key] for key in
                      ('Gamma_upper', 'old_Gamma_upper', 'improvement', 'worst_roots')}))


if __name__ == '__main__':
    main()
