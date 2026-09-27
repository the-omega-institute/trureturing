#!/usr/bin/env python3
"""Two complete original J AP11 blocks retain135/125 and a second seven depth."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-geometry/j_face_second_depth_survival_heads.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/j-geometry/j_face_second_depth_retained_heads.py': '664831d3b5feabbe225e34036a7adc0e0e386ee467859bbb5a1cf88618b3a437', 'certificates/source_norms/j-geometry/j_face_second_depth_retained_heads.json': 'f3bbf753266e3596df00ea76ae7042f2f05aa77aeba51397c4b05b4b39afbeca', 'profile-notes/193-256/256-a-second-seven-depth-sharpens-the-complete-retained-j-heads.md': '8b51d3dbd5328bfe55cad1909a7321deb9fe7f9f0be08230240ae4fede5d91be', 'frontier/j-geometry/j_face_joint_survival_heads.py': '8be3c343fdfd5011cbcd2fe9731a233a2143301c135c255ced93f6068f30b914', 'certificates/source_norms/j-geometry/j_face_joint_survival_heads.json': '970d721747940bea35789f587590604931690ab73d1a18413fc3feed5e96b17f', 'profile-notes/193-256/249-all-four-complete-j-ap11-blocks-retain-the-same-marked-source.md': '85400b51bbae3dc663d2a9a81661d637f037cf220530ff20e418269f5bc6c589'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original mathematical source')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base, bank):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned canonical artifact reader')
    io = module('j_depth_survival_io', base/'certificate_io.py')
    core = module('j_depth_survival_core', base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')),
                                  object_pairs_hook=core.unique)
    prior, depth_heads = read('j_face_joint_survival_heads'), read('j_face_second_depth_retained_heads')
    prior244, prior251 = read('j_face_joint_selected_heads'), read('j_face_retained135125_heads')
    pins = dict(PINS)
    for source in (prior, depth_heads, prior244, prior251):
        for path, pin in source['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent mathematical source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned complete input '+path)
    require(all(source['geometry'] == prior['geometry'] and F(source['survivor_mass']) == F(3,20)
                for source in (depth_heads, prior244, prior251)), 'The same complete actual saturated J domain')
    j = module('j_depth_survival_j', base/'frontier/j-geometry/j_face_coupled_seven_heads.py')
    pair = module('j_depth_survival_pair', base/'frontier/j-geometry/j_face_retained135125_heads.py')
    depth = module('j_depth_survival_formula', base/'frontier/comparison-bounds/second_depth_seven_comparison.py')
    second = module('j_depth_survival_scanner', base/'frontier/j-geometry/j_face_second_depth_retained_heads.py')
    problem = second.SecondDepthJHead(base, j, core, pair, depth, prior244, prior251, bank=bank)
    require(problem.specification == depth_heads['model'] and second.Z6 == F(37,1225)
            and F(depth_heads['complete_positive7_tail']) == second.Z6,
            'The unchanged complete256 source model and all positive-seven tail caps')
    original = module('j_depth_survival_functions', base/'frontier/j-geometry/j_face_complete_survival_linear_heads.py')
    source = module('j_depth_survival_count', base/'verify_joint_frontier.py')
    engine = module('j_depth_survival_inventory', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    jobs, count = original.prepare_jobs(source, engine)
    require(encode(count) == prior['count_law'], 'Exactly the original complete AP count law')
    rows = []
    require([row['name'] for row in prior['results']] == ['AP11-'+str(i) for i in range(4)],
            'All four independent original block names')
    for job, row in zip(jobs[:2], prior['results'][:2]):
        require(job['kind'] == row['kind'] == 'AP11' and job['name'] == row['name']
                and row['at_one'] == '0' and job['at_one'] == 0
                and encode(job['coefficients']) == row['coefficients'] == row['scan']['coefficients'],
                'The identical original all-load block function, without a changed threshold')
        scan_input = dict(row)
        scan_input['index'] = row['name']
        scan = problem.scan(scan_input)
        complete = scan['complete_hinge_upper']
        previous = F(row['adopted_upper'])
        mean_only = sum(job['coefficients'].values())*(F(16,25)-F(3,20))
        require(0 < complete < min(previous, mean_only), 'Strict whole-domain block improvement')
        rows.append({'name': row['name'], 'kind': 'AP11', 'block': row['block'],
                     'coefficients': job['coefficients'], 'at_one': F(0), 'scan': scan,
                     'complete_head_upper': complete, 'previous_adopted_upper': previous,
                     'complete_mean_only_upper': mean_only, 'adopted_upper': complete,
                     'improvement_over_previous': previous-complete})
    require(problem.used == set(problem.bank), 'Every exact retained dual is consumed')
    retained = {key: problem.bank[key] for key in sorted(problem.used)}
    encoded = problem.codec.encode_dual_bank(retained, inequality_count=6354, equality_count=18)
    require(problem.codec.decode_dual_bank(encoded, inequality_count=6354, equality_count=18) == retained,
            'Lossless entire rational dual bank')
    unchanged = [{'name': row['name'], 'adopted_upper': F(row['adopted_upper'])}
                 for row in prior['results'][2:]]
    old_sum = sum(F(row['adopted_upper']) for row in prior['results'])
    new_sum = sum(row['adopted_upper'] for row in rows+unchanged)
    h4 = next(F(row['adopted_upper']) for row in depth_heads['results'] if row['index'] == 'AP13')
    tail = count['remaining_hinge1_coefficient']*(F(16,25)-F(3,20))+count['whole_constant_coefficient']*F(3,20)
    before = F(3,20)-h4/6-(old_sum+tail)/7
    after = F(3,20)-h4/6-(new_sum+tail)/7
    require(tail == F(277,4392300) and 0 < before < after and after-before == (old_sum-new_sum)/7,
            'All four AP11 blocks, the same AP13, actual mass and infinite count tail remain')
    return encode({'schema': 'erdos7-j-face-second-depth-survival-heads-v1', 'source_sha256': pins,
        'geometry': prior['geometry'], 'source_mass': F(1,4), 'survivor_mass': F(3,20),
        'complete_mean_upper': F(16,25), 'model': problem.specification, 'count_law': count,
        'retained_positive7_labels': [21,35,63,105,147,245], 'complete_positive7_tail': second.Z6,
        'results': rows, 'unchanged_AP11_bounds': unchanged, 'complete_AP13_upper': h4,
        'previous_AP11_sum': old_sum, 'complete_AP11_sum': new_sum, 'complete_count_tail_upper': tail,
        'previous_survival_denominator': before, 'complete_survival_denominator': after,
        'survival_denominator_improvement': after-before, 'encoded_rational_duals': encoded,
        'distinct_dual_count': len(retained), 'rational_column_checks': 3306*len(retained),
        'previous251_duals_used': sorted(problem.prior_used),
        'total_containing_choices': sum(row['scan']['covered_containing_choices'] for row in rows),
        'total_independent_affine_checks': sum(row['scan']['independent_affine_checks'] for row in rows),
        'scope': 'Both entire actual saturated J faces. Original AP11 blocks0/1 retain the unchanged256 '
            'actual-source135/125 model and independent147/245 projections, all62500000 original choices '
            'per block and every exponent tail. Original249 blocks2/3 remain. The denominator keeps '
            'the same256 AP13, exact actual mass and complete infinite count law. No joint attainment, '
            'off-face extension, full52-cost comparison, Lean verification or unrestricted Erdos7 result.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('j_depth_survival_reader', args.base/'certificate_io.py')
    core = module('j_depth_survival_json', args.base/'frontier/j-geometry/j_face_joint_selected_heads.py')
    stored = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE), object_pairs_hook=core.unique)
    codec = module('j_depth_survival_codec', args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
    bank = codec.decode_dual_bank(stored['encoded_rational_duals'], inequality_count=6354, equality_count=18)
    require(calculate(args.base, bank) == stored, 'Every complete two-block and denominator field recomputes')
    print('PASS: two original AP11 blocks;125000000 containing choices;'
          +str(stored['distinct_dual_count'])+' exact3306-column duals; all four blocks and infinite tails.', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
