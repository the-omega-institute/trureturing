#!/usr/bin/env python3
"""Exact PG1 auxiliary square at depth (1,0,0), retaining original3/original9.

For a pure square and r>=0, independently free equal-cofactor cylinders can
be pooled at the level of the maximum: convexity gives
  (H+1_C+r*1_D)^2 <= ((H+(1+r)*1_C)^2+r*(H+(1+r)*1_D)^2)/(1+r).
The reverse maximum inequality follows by choosing C=D. Apply this only to
free labels, never to the fixed original mod9 and its independent higher9.
This identity does not pool a signed cost retaining the original load B.

At auxiliary depth100 the old load is
  1+1_{original3}+1_{original9}+1_C5+1_C15+2*1_C45+1_{higher9},
and the six independent seven-label weights are (1,1,1,2,1,2). We compute
every old layout for all ten roots, including all empty residue classes.
The oracle checks independent Python DP and a literal75-point winner.
Here a second check constructs all blocks from raw original residues and
directly enumerates all 7^6 digit assignments, without singleton elimination
or the subset DP recurrence. Signed fixtures additionally exercise the
weighted oracle beyond the square objective.

Replace only this one inherited inside-box bound, with probability16/105.
The exact zero-depth extension, other268 depths, and the complete geometric
tail remain unchanged. Thus physical heights remain arbitrarily large but
finite. New auxiliary labels are not a forbidden family with repeated moduli.

For the existing common-floor consumer every one of its10000 combinations
loses at least delta=(1403/630)*min_root(square saving). Subtract delta from
both its constant maximum and split constant, retaining the same actual Q.
Check endpoints and the crossing of the two bounds on Q in[q0,1]; negative
excesses are never independently divided by q0. No carrier count is updated.

The older geometry certificates are separately verified, hash-bound inputs.
Only this new extension certificate is written by --write. Requires NumPy
for the independent exhaustive comparison and an available C++17 compiler.
"""

# Pinned local IO preserves complete certificate hashes after semantic splitting.
import sys as _certificate_sys
from pathlib import Path as _CertificatePath
from hashlib import sha256 as _certificate_sha256
_certificate_root = _CertificatePath(__file__).resolve().parent
_certificate_io_path = _certificate_root / 'certificate_io.py'
if _certificate_sha256(_certificate_io_path.read_bytes()).hexdigest() != '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b':
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
import numpy as np

HERE = Path(__file__).resolve().parent
SCHEMA = 'erdos7-pg1-exact-depth100-v1'
SOURCES = ('certificates/mod3_conditioned_geometry_certificate.json',
           'certificates/original9_conditioned_geometry_certificate.json',
           'certificates/pg1_exact_zero_depth_certificate.json',
           'certificates/pg1_common_source_floor_certificate.json')
IMPLEMENTATION = ('pg1_weighted_score_oracle.py', 'pg1_weighted_score_oracle.cpp',
                  'exact_signed_digit_dp.py', 'verify_point_geometry.py')
COFACTORS = (1, 3, 5, 9, 15, 45)
WEIGHTS = (1, 1, 1, 2, 1, 2)


def module(name):
    spec = spec_from_file_location(name, HERE / (name+'.py'))
    obj = module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


weighted = module('pg1_weighted_score_oracle')
pg = module('verify_point_geometry')
require = weighted.require


def digest(obj):
    return sha256(json.dumps(obj, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def old_labels(root3, root9):
    return [{'cofactor': 1, 'weight': 1, 'residue': 0},
            {'cofactor': 3, 'weight': 1, 'residue': root3, 'role': 'original3'},
            {'cofactor': 9, 'weight': 1, 'residue': root9, 'role': 'original9'},
            {'cofactor': 5, 'weight': 1}, {'cofactor': 15, 'weight': 1},
            {'cofactor': 45, 'weight': 2}, {'cofactor': 9, 'weight': 1, 'role': 'higher9'}]


class IndependentEnumeration:
    """Raw residues, explicit singleton, and exhaustive digit assignments."""
    def __init__(self, xs):
        self.xs = xs
        self.cylinders = {c: sorted({tuple(int(x % c == a) for x in xs) for a in range(c)})
                          for c in COFACTORS}
        self.matrices = []
        for s in range(64):
            es = [e for e in range(6) if s >> e & 1]
            loads = {tuple(sum(WEIGHTS[e]*mask[i] for e, mask in zip(es, choices))
                           for i in range(16))
                     for choices in product(*(self.cylinders[COFACTORS[e]] for e in es))}
            self.matrices.append(np.array(sorted(loads), dtype=np.int64))
        assignments = np.array(list(product(range(7), repeat=6)), dtype=np.int64)
        require(assignments.shape == (117649, 6), 'all seven independent digits for each label')
        self.partitions = np.array([sum((assignments[:, e] == y)*(1 << e) for e in range(6))
                                    for y in range(7)])

    def check_domain(self, oracle):
        for e, c in enumerate(COFACTORS):
            require(sorted(mask for _, mask in oracle.dp.cylinders[e]) == self.cylinders[c],
                    'every raw original residue represented, including empty')
        for s, states in oracle.dp.states.items():
            require(sorted(set(load for load, _ in states)) == [tuple(map(int, row)) for row in self.matrices[s]],
                    'every weighted non-singleton load retained')
        choices = []
        for r in oracle.old_labels:
            c = r['cofactor']
            choices.append([tuple(int(x % c == r['residue']) for x in self.xs)]
                           if 'residue' in r else self.cylinders[c])
        raw = {tuple(sum(r['weight']*mask[i] for r, mask in zip(oracle.old_labels, realization))
                     for i in range(16)) for realization in product(*choices)}
        require(sorted(raw) == [A for A, _ in oracle.old],
                'entire fixed-root old domain equals the independent raw-residue enumeration')

    def optimize(self, A, scores):
        require(4*sum(max(map(abs, row)) for plane in scores for row in plane) < 2**61,
                'independent NumPy sums stay in signed64 range')
        table = np.array(scores, dtype=np.int64)
        row_index = np.arange(16)
        blocks = np.array([[int(np.max(np.sum(table[y, row_index, L+np.array(A)], axis=1)))
                            for L in self.matrices] for y in range(7)], dtype=np.int64)
        value = int(max(sum(blocks[y, self.partitions[y]] for y in range(7))))
        common = max(int(blocks[y, 63]+sum(blocks[z, 0] for z in range(7) if z != y))
                     for y in range(7))
        return value, common


def signed_regressions(binary, source, initial, independent):
    specs = [{'cofactor': r['modulus'], 'residue': r['residue'], 'weight': r['weight'],
              'role': r['role']} for r in initial['weighted_labels'][:7]]
    with weighted.Oracle(WEIGHTS, specs, source, binary) as oracle:
        require(len(oracle.old) == 1 and oracle.maxload == 16,
                'fixed-old signed tests exceed the old unit-load12 range')
        A = oracle.old[0][0]
        def zeros():
            return [[[0]*(oracle.maxload+1) for _ in range(16)] for _ in range(7)]
        point_weights = list(zip(oracle.points, oracle.case['weight_numerators']))
        x = next(x for x in oracle.xs if sum(t % 45 == x for t in oracle.points) >= 2)
        pair = [(t, w) for t, w in point_weights if t % 45 == x][:2]
        counter = zeros()
        for t, w in pair:
            i, y = oracle.ri[x], t % 7
            counter[y][i] = [-w*(k-A[i]-2)**2 for k in range(oracle.maxload+1)]
        c = oracle.optimize(counter)
        require(c['maximum_numerator'] == 0 and c['common_digit_maximum_numerator'] == -4*min(w for _, w in pair),
                'weighted signed objective strictly requires independent digits')
        negative = zeros()
        for t, w in point_weights:
            i, y = oracle.ri[t % 45], t % 7
            negative[y][i] = [-w*(k-A[i]) for k in range(oracle.maxload+1)]
        z = oracle.optimize(negative)
        require(z['maximum_numerator'] == 0 and z['weighted_labels'][7]['digit'] == 0,
                'legal digit zero is required for the nonempty cofactor1 label')
        rng = Random(20260917)
        random_scores = zeros()
        for t, w in point_weights:
            random_scores[t % 7][oracle.ri[t % 45]] = [w*rng.randrange(-12, 13) for _ in range(oracle.maxload+1)]
        r = oracle.optimize(random_scores)
        for scores, result in ((counter, c), (negative, z), (random_scores, r)):
            require(independent.optimize(A, scores) ==
                    (result['maximum_numerator'], result['common_digit_maximum_numerator']),
                    'complete raw blocks and7^6 enumeration verify weighted signed C++ results')
        rejected = []
        for name, scores in (('missing_load_column', [[row[:-1] for row in plane] for plane in counter]),
                             ('signed64_overflow', [[[v*(2**61) for v in row] for row in plane] for plane in counter])):
            try:
                oracle.optimize(scores)
            except ArithmeticError:
                rejected.append(name)
            else:
                raise ArithmeticError('invalid weighted score domain accepted')
        return {'old_labels': specs, 'maximum_load': oracle.maxload,
                'independent_digit_counterexample': {'points': [t for t, _ in pair],
                    'maximum_numerator': c['maximum_numerator'],
                    'common_digit_maximum_numerator': c['common_digit_maximum_numerator']},
                'digit_zero_maximum_numerator': z['maximum_numerator'],
                'signed_random_maximum_numerator': r['maximum_numerator'],
                'signed_random_common_digit_maximum_numerator': r['common_digit_maximum_numerator'],
                'invalid_domains_rejected': rejected}


def evaluate(directory, expected_hashes=None):
    raw = {name: read_artifact_bytes(directory/name) for name in SOURCES}
    hashes = {name: sha256(data).hexdigest() for name, data in raw.items()}
    if expected_hashes is not None:
        require(hashes == expected_hashes, 'unchanged complete prerequisite certificate chain')
    base, original, zero, common = (json.loads(raw[name]) for name in SOURCES)
    require(original['source_sha256'] == hashes[SOURCES[0]] and
            all(zero['source_sha256'][name] == hashes[name] for name in SOURCES[:2]) and
            all(common['source_sha256'][name] == hashes[name] for name in SOURCES[:3]),
            'all extensions refer to the same actual PG1 probability')
    require(zero['schema'] == 'erdos7-pg1-exact-zero-depth-v1' and
            common['schema'] == 'erdos7-pg1-common-source-floor-v1', 'prerequisite schemas')
    case = next(c for c in base['cases'] if c['name'] == 'PG1')
    weights, den = case['weight_numerators'], case['weight_denominator']
    require(sum(weights) == den == 1000000007 and all(type(w) is int and w >= 0 for w in weights),
            'unchanged exact PG1 probability')
    cut = (8, 5, 4)
    _, _, _, _, depths, probabilities, beta, outside = pg.coeffs(cut)
    depth = (1, 0, 0)
    index = depths.index(depth)
    probability = probabilities[index]
    require(len(depths) == 270 and probability == F(16, 105) and min(outside) >= 0 and 0 < beta < 1,
            'one selected depth and complete nonnegative geometric tail')
    require(zero['result']['depth_box'] == list(cut) and zero['result']['exact_depth'] == [0, 0, 0],
            'retain the exact zero-depth and full outside-anchor extension')
    root_pairs = [(i, j) for j in sorted({x % 9 for x in case['old_points']}) for i in (1, 2)]
    prior = {(r['root3'], r['root9']): r for r in original['result']['records']}
    zero_rows = {(r['root3'], r['root9']): r for r in zero['result']['records']}
    require(len(root_pairs) == len(prior) == len(zero_rows) == 10 and set(root_pairs) == set(prior) == set(zero_rows),
            'all ten distinct fixed original3/original9 branches')
    independent = IndependentEnumeration(case['old_points'])
    records = []
    with weighted.Oracle(WEIGHTS, old_labels(*root_pairs[0]), directory/SOURCES[0]) as compiled:
        for key in root_pairs:
            with weighted.Oracle(WEIGHTS, old_labels(*key), directory/SOURCES[0], compiled.binary) as oracle:
                independent.check_domain(oracle)
                require(oracle.maxload == 15+int(key[1] % 3 == key[0]) and len(oracle.old) == 3972,
                        'complete weighted depth100 domain and root-compatible load limit')
                scores = oracle.score_tensor({'point_scores': [[w*k*k for k in range(oracle.maxload+1)] for w in weights]})
                result = oracle.optimize(scores, den)
                require(independent.optimize(result['maximizing_A'], scores) ==
                        (result['maximum_numerator'], result['common_digit_maximum_numerator']),
                        'raw full-residue blocks and all7^6 digits agree at each rooted maximum')
                original_label, higher_label = result['weighted_labels'][2], result['weighted_labels'][6]
                require(original_label['role'] == 'original9' and original_label['residue'] == key[1] and
                        higher_label['role'] == 'higher9' and higher_label['modulus'] == 9,
                        'fixed original9 and independent higher9 remain distinct auxiliary roles')
                old = prior[key]
                inherited = list(map(min, zip(old['pure7_numerators'], old['fixedA_numerators'])))
                require(len(inherited) == 270, 'all inherited inside-box depths retained')
                exact = result['maximum_numerator']
                require(exact < inherited[index], 'strict complete weighted improvement in each branch')
                saving = probability*F(inherited[index]-exact, den)
                new_U = F(zero_rows[key]['new_U'])-saving
                deletion = F(old['weighted_deletion_upper'])
                records.append({'root3': key[0], 'root9': key[1], 'oracle': result,
                                'old_depth_upper_numerator': inherited[index],
                                'exact_depth_numerator': exact, 'unconditional_saving': str(saving),
                                'new_U': str(new_U), 'inherited_weighted_deletion_upper': str(deletion),
                                'new_signed_excess': str(new_U+deletion-33),
                                'other268_inside_depths_sha256': digest([v for k, v in enumerate(inherited) if k not in (0, index)])})
        regressions = signed_regressions(compiled.binary, directory/SOURCES[0], records[0]['oracle'], independent)
    q0 = F(original['result']['survival_lower'])
    require(q0 == F(zero['result']['source_survival_lower']) == F(common['source_survival_lower']) and q0 > 0,
            'one unchanged independently certified survival bound')
    worst = max(records, key=lambda r: F(r['new_signed_excess']))
    G = 33+max(F(0), F(worst['new_signed_excess']))/q0
    prior_G = F(zero['result']['Gamma_upper'])
    require(G < prior_G, 'strict same-law all-height source improvement')
    # This bound uniformly improves all10000 independent root combinations;
    # no inherited deletion maximum or common-Q denominator is separated.
    M = F(common['coefficients']['zero_head'])
    other = F(common['coefficients']['other_heads'])
    require(M == F(4, 3) and other == F(563, 630) and common['root_combinations'] == 10000,
            'complete inherited common-floor root product and square coefficients')
    delta = (M+other)*min(F(r['unconditional_saving']) for r in records)
    maximum = F(common['maximum_source_excess_upper'])-delta
    A = F(common['split_Q_coefficient'])
    B = F(common['split_constant_max'])-delta
    K = F(common['source_reference'])
    require(A < 0 and B > 0 and K == F(297, 2), 'same common-floor affine branches')
    qs = {q0, F(1)}
    cross = (maximum-B)/A
    if q0 <= cross <= 1:
        qs.add(cross)
    candidates = [(K+min(maximum, A*q+B)/q, q) for q in sorted(qs)]
    bound, worst_q = max(candidates)
    old_bound = F(common['Gamma13_upper'])
    require(bound < old_bound, 'strict actual-common-Q fixed11/13 improvement')
    loss_limit = q0*(35-G)/34
    require(0 < loss_limit < q0, 'positive target35 conditioning threshold')
    scaled_loss = den*loss_limit
    return {'schema': SCHEMA, 'source_sha256': hashes,
            'implementation_sha256': {name: sha256(read_artifact_bytes(HERE/name)).hexdigest() for name in IMPLEMENTATION},
            'result': {'depth': list(depth), 'depth_box': list(cut), 'depth_probability': str(probability),
                'source_survival_lower': str(q0), 'records': records, 'old_layouts': 39720,
                'maximum_load': 16, 'weighted_subset_states': 3024,
                'independent_digit_assignments': 117649,
                'independent_weighted_subset_load_counts': [len(v) for v in independent.matrices],
                'signed_regressions': regressions,
                'prior_Gamma_upper': str(prior_G), 'Gamma_upper': str(G), 'improvement': str(prior_G-G),
                'worst_roots': [worst['root3'], worst['root9']],
                'common_floor_consumer': {'uniform_source_integral_improvement': str(delta),
                    'maximum_source_excess_upper': str(maximum), 'split_Q_coefficient': str(A),
                    'split_constant_max': str(B), 'source_reference': str(K),
                    'common_Q_candidates': [{'Q': str(q), 'bound': str(v)} for v, q in candidates],
                    'worst_Q': str(worst_q), 'prior_Gamma13_upper': str(old_bound),
                    'Gamma13_upper': str(bound), 'improvement': str(old_bound-bound)},
                'target35_conditioning': {'loss_limit': str(loss_limit), 'weight_denominator': den,
                    'integer_loss_limit': scaled_loss.numerator//scaled_loss.denominator,
                    'scope': 'Improved threshold only; no new carrier enumeration or coverage count.'},
                'scope': 'Same actual PG1 law and original labels; complete auxiliary depth100 maximum for ten roots, exact zero-depth extension and other268 inside-box bounds and full tails retained. Arbitrary finite physical heights. Common-floor11/13 extension retains all original physical kernels, deletions and a common actual Q. No unrestricted-prime or whole-carrier resolution.'}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path, default=HERE/'certificates/pg1_exact_depth100_certificate.json')
    parser.add_argument('--source-directory', type=Path, default=HERE)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    expected = None if args.write else json.loads(read_artifact_text(args.certificate))
    if expected is not None:
        require(expected['schema'] == SCHEMA, 'extension certificate schema')
    actual = evaluate(args.source_directory, None if expected is None else expected['source_sha256'])
    if args.write:
        write_certificate_text(args.certificate, json.dumps(actual, indent=2)+'\n')
    else:
        require(actual == expected, 'complete exact depth100 extension certificate')
    result = actual['result']
    print(json.dumps({'status': 'written' if args.write else 'verified',
                      'Gamma_upper': result['Gamma_upper'], 'old_Gamma_upper': result['prior_Gamma_upper'],
                      'Gamma13_upper': result['common_floor_consumer']['Gamma13_upper'],
                      'old_layouts': result['old_layouts'], 'roots': len(result['records'])}))


if __name__ == '__main__':
    main()
