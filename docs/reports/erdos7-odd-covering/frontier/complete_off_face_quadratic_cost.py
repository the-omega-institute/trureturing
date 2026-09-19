#!/usr/bin/env python3
"""Original quadratic costs share one actual off-face head and all tails.

Uses113's exact original expansions,126's integer finite operator and128's
complete factorial head. Each source has one actual capacity/error vector.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
from time import perf_counter

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/complete_off_face_quadratic_cost.json'
POSITIVE_INDICES = (41, 42, 43, 44, 45, 47, 48, 49, 50, 51)
FACE_MASS = F(53, 360)
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/finite_source_face_transport.py': 'aa4099317ddf1b7cca16df4916166b1399d0b6e44cbe6459dde081075db8d332',
    'frontier/complete_off_face_cost.py': '6ab17509f6946409cef6b431cdfb316cc35c9055d21de93eb2906c723d93e234',
    'frontier/complete_off_face_omitted_tails.py': '0dc92761c65f6729dfe45770b02dae327d5ddfa1d4b0a79dcc45fb9deb8b81f8',
    'frontier/complete_off_face_factorial_tail.py': '8447e1cd50d6452a881413067858188344d22631c7b73b74734b3006a244d047',
    'frontier/joint_deep_mean_transport.py': 'a63225e637c6e926e80b04822ab8c83b79f8b99d3069b283375838df69ea4534',
    'frontier/whole_quadratic_same_head.py': 'd447341c1887a1be5aae4ce46aa3405f594617929d7c8aa776a4b6032668d7a2',
    'frontier/broad_weighted_identity_source.py': 'e0a89669a6b8b6ff732391b4c27dddd21bf5517f8a37928120e75955349dd98f',
    'certificates/source_norms/whole_quadratic_same_head.json': 'b77b50ff8961dcfafaefdb004b538a1a2409e69944f894048ae25b1ae0bede3a',
    'certificates/source_norms/whole_cost_mean_stop_loss.json': 'd535a2f69617536a06655c61a1166813bfd2ce3e17416fc329dcead0ba3201da',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def original_tag(encoded):
    kind, data = encoded
    if kind == 's':
        return kind, F(data)
    require(kind == 'ap_block' and len(data) == 4, 'One original quadratic tag')
    inner, caps, e, f = data
    require(isinstance(e, int) and isinstance(f, int), 'Original AP exponent tuple')
    return kind, (original_tag(inner), tuple((p, F(c)) for p, c in caps), e, f)


def prepare_rows(source, original, previous, indices):
    require(indices and len(set(indices)) == len(indices) and all(i in POSITIVE_INDICES for i in indices),
            'Exactly requested positive original quadratic rows')
    rows = []
    for row in previous['quadratic_results']:
        tag = original_tag(row['tag'])
        expansion = original.quadratic_expansion(source, tag)
        require(encode(expansion) == row['expansion'], 'Original function and complete polynomial expansion agree with113')
        if row['index'] in indices:
            require(not expansion['negative_hinge_coefficients'] and expansion['factorial_tail_coefficient'] > 0,
                    'Every substituted hinge and factorial coefficient is nonnegative')
            rows.append({'index': row['index'], 'tag': tag, 'expansion': expansion,
                         'face_joint_upper': F(row['uniform_cost_upper']),
                         'face_accepted_upper': F(row['accepted_cost_upper'])})
    require(tuple(row['index'] for row in rows) == tuple(sorted(indices)), 'Retain original inventory indices')
    return rows


def source_costs(finite, original, mean, factorial, tails, capacity, case, rows):
    problem = factorial.FactorialHead(finite, tails, case)
    tail, pair_tail = problem.tail_data, problem.pairs['tail_distinct_pairs']
    d, _, eta, _, _ = case['dat']
    defects = case['defects']
    defect_parts = (case['E27'], defects['E3']-case['E27'], defects['E5d'], defects['E15d'])
    jobs = []
    for row in rows:
        expansion = row['expansion']
        record = finite.prepare(expansion['hinge_coefficients'])
        compiler = original.IntegerHead(finite, record, case['point'], case['q'])
        jobs.append({'row': row, 'record': record, 'compiler': compiler,
                     'theta': expansion['factorial_tail_coefficient'],
                     'a1': record['coefficients'].get(1, F(0)), 'best_num': None, 'best_den': None,
                     'ties': 0, 'digest': sha256(), 'count': 0, 'witness': None})
    for layout in mean.layouts():
        data = mean.mean_data(case['sigma'], max(d), max(d[2:]), case['parameter'][4], eta, case['qslots'], layout)
        credit = mean.mean_credit(data, *defect_parts)['nonnegative_credit']
        B = problem.load(layout)
        factorial_parts = problem.components(layout, B)
        for job in jobs:
            compiler = job['compiler']
            payment = job['a1']*credit-job['theta']*factorial_parts['head_total']
            for r, j, extra in compiler.positive7:
                value = compiler.branch(B, extra)
                num = value*payment.denominator-payment.numerator*compiler.scale
                den = compiler.scale*payment.denominator
                job['digest'].update((str(num)+'/'+str(den)+';').encode())
                delta = 1 if job['best_num'] is None else num*job['best_den']-job['best_num']*den
                if delta > 0:
                    job['best_num'], job['best_den'], job['ties'] = num, den, 1
                    job['witness'] = {'layout': layout, 'positive7_root': r, 'positive7_slot': j,
                                      'finite_upper': F(value, compiler.scale), 'mean_credit': credit,
                                      'factorial_head_components': factorial_parts}
                elif delta == 0:
                    job['ties'] += 1
                job['count'] += 1
    results = []
    for job in jobs:
        row, record, compiler, witness = (job[k] for k in ('row', 'record', 'compiler', 'witness'))
        require(job['count'] == 125000, 'All original heads and independent positive-seven projections')
        joint = F(job['best_num'], job['best_den'])
        public = finite.branch(capacity, record, case['point'], case['q'], witness['layout'],
                               (witness['positive7_root'], witness['positive7_slot']))
        require(public['value'] == witness['finite_upper'], 'Saved maximum also equals116 independent rational LP solver')
        require(joint == witness['finite_upper']-job['a1']*witness['mean_credit']
                +job['theta']*witness['factorial_head_components']['head_total'], 'One actual maximizing branch')
        weighted_tail = sum(a*(tail['old_remainders'][record['prefix'][t]]+tail['positive7'])
                            for t, a in record['coefficients'].items())
        at_one = row['expansion']['at_one']
        mass_term = at_one*case['survivor_mass']
        bounded_error = record['M']*defects['omega']
        factorial_pair = job['theta']*pair_tail
        bound = mass_term+joint+weighted_tail+bounded_error+factorial_pair
        accepted, comparison = bound, 'Only this actual-source candidate is compared'
        if case['height'] is None:
            require(bound == row['face_joint_upper'], 'Exact original113 whole-face quadratic candidate recovered')
            accepted = min(bound, row['face_accepted_upper'])
            comparison = 'Minimum with113 accepted bound on the same whole face'
        results.append({'cost_index': row['index'], 'original_tag': row['tag'], 'expansion': row['expansion'],
                        'joint_finite_and_factorial_head_upper': joint, 'complete_weighted_hinge_tail': weighted_tail,
                        'bounded_hinge_error_price': record['M'], 'bounded_hinge_error': bounded_error,
                        'complete_factorial_pair_payment': factorial_pair, 'actual_constant_mass_term': mass_term,
                        'complete_candidate_upper': bound, 'accepted_upper_in_stated_scope': accepted,
                        'comparison_scope': comparison, 'original_branch_checks': job['count'],
                        'integer_cost_scale': compiler.cost_scale, 'integer_mass_scale': compiler.mass_scale,
                        'all_joint_objectives_sha256': job['digest'].hexdigest(), 'maximizing_witness': witness,
                        'maximizer_count': job['ties']})
    return {'source_height': case['height'], 'sigma': case['sigma'], 'survivor_mass': case['survivor_mass'],
            'one_actual_defect_vector': defects, 'E27': case['E27'], 'complete_hinge_tail_data': tail,
            'complete_factorial_pair_data': problem.pairs, 'quadratic_costs': results}


def calculate(base, indices):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('off_quadratic_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    finite = module('off_quadratic_finite', base/'frontier/finite_source_face_transport.py')
    original = module('off_quadratic_original', base/'frontier/complete_off_face_cost.py')
    mean = module('off_quadratic_mean', base/'frontier/joint_deep_mean_transport.py')
    factorial = module('off_quadratic_factorial', base/'frontier/complete_off_face_factorial_tail.py')
    tails = module('off_quadratic_tails', base/'frontier/complete_off_face_omitted_tails.py')
    source = module('off_quadratic_source', base/'verify_joint_frontier.py')
    capacity = module('off_quadratic_capacity', base/'frontier/broad_weighted_identity_source.py')
    old_expansion = module('off_quadratic_expansion', base/'frontier/whole_quadratic_same_head.py')
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_quadratic_same_head.json'))
    rows = prepare_rows(source, old_expansion, previous, tuple(indices))
    cases = [original.face_case(finite, source)]+[original.actual_398_case(finite, source, N) for N in (5, 8)]
    results = []
    for case in cases:
        started = perf_counter()
        result = source_costs(finite, original, mean, factorial, tails, capacity, case, rows)
        results.append(result)
        print('Checked '+str(len(rows))+' complete quadratic costs at height '+str(case['height'])
              +' in '+format(perf_counter()-started, '.3f')+' seconds', flush=True)
    #109's stored constant_mass_term is a0*D_face, never a0.
    old_linear = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/whole_cost_mean_stop_loss.json'))
    constant_rows = [row for row in old_linear['cost_results'] if row['index'] == 40]
    require(len(constant_rows) == 1, 'Unique original nonzero-constant row40')
    at_one = F(constant_rows[0]['constant_mass_term'])/FACE_MASS
    require(at_one == 1, 'The old stored mass coefficient is normalized before actual-source use')
    constant_checks = [{'source_height': case['height'], 'stored_face_mass_term': constant_rows[0]['constant_mass_term'],
                        'at_one': at_one, 'actual_mass_term': at_one*case['survivor_mass']} for case in cases]
    require(all(row['actual_mass_term'] == case['survivor_mass'] for row, case in zip(constant_checks, cases)),
            'Nonzero constant multiplies actual S exactly once')
    return {'schema': 'erdos7-complete-off-face-quadratic-cost-v1', 'source_sha256': PINS,
            'original_positive_indices': indices, 'complete_source_cases': results,
            'nonzero_constant_regression': constant_checks,
            'scope': 'Complete original quadratic costs at fixed actual sources, using one original layout for finite hinges, actual mean deletion and the full factorial head. All source and exponent tails share one actual defect vector. Exact113 face recovery; finite398 heights5 and8 are not a uniform all-source maximum. No new signed global comparison, K bound, Lean verification or Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--indices', type=int, nargs='+', default=list(POSITIVE_INDICES))
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base, tuple(args.indices)))
    io = module('off_quadratic_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete off-face quadratic certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: complete quadratic polynomial tails, common original heads and actual-source mean/factorial credits.')
    print('All other sources and the full signed comparison still require a separate proof.')


if __name__ == '__main__':
    main()
