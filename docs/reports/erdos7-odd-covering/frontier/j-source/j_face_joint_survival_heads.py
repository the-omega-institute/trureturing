#!/usr/bin/env python3
"""Four complete original J AP11 blocks in the shared244 source model."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_joint_survival_heads.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_joint_selected_heads.py': '4b244d4008d7cfe0025888192b8ed8a412a8f51509133d0b04208bcd6b47ad2c', 'certificates/source_norms/j-source/j_face_joint_selected_heads.json': '434cd2865b3a61e19ecba395787420bc45d5c4b1da6a6831e93675109ef07a97', 'frontier/j-source/j_face_complete_survival_linear_heads.py': '9b54162036dae52ea63149a377b0a6fb1ae5d5dfe24d01ffb4732f3b605b2437', 'certificates/source_norms/j-source/j_face_complete_survival_linear_heads.json': 'd3dc85acd3f0b677e5020da0da356e475111d24c1a288029ebb384109e203747', 'profile-notes/j-source/244-three-complete-j-heads-share-raw-survivor-and-marked-deletion.md': 'd8c7038d7b2bd5ebc22fbd0f96c5443b88a282883d0efb252380a87810074f4a'}
MASS, MEAN = F(3, 20), F(16, 25)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable existing mathematical provider')
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
    require(PINS, 'Final pinned mathematical inputs')
    io = module('j_ap_joint_io', base/'certificate_io.py')
    joint = module('j_ap_joint', base/'frontier/j-source/j_face_joint_selected_heads.py')
    previous = module('j_ap_previous', base/'frontier/j-source/j_face_complete_survival_linear_heads.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=joint.unique)
    old, prior = read('j-source/j_face_complete_survival_linear_heads'), read('j-source/j_face_joint_selected_heads')
    pins = dict(PINS)
    for source in (old, prior):
        for path, pin in source['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent existing J source closure '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical source '+path)
    require(old['geometry'] == prior['geometry']
            and F(old['source_mass']) == F(prior['source_mass']) == F(1, 4)
            and F(old['mass']) == F(prior['survivor_mass']) == MASS
            and F(old['complete_mean_upper']) == F(prior['complete_mean_upper']) == MEAN,
            'The same two entire actual saturated J faces and unnormalized source measures')
    j = module('j_ap_source', base/'frontier/j-source/j_face_coupled_seven_heads.py')
    problem = joint.JointSelectedJHead(base, j, bank=bank)
    require(problem.specification == prior['model'], 'The identical244 complete876-column actual-source model')
    source = module('j_ap_count', base/'verify_joint_frontier.py')
    engine = module('j_ap_inventory', base/'frontier/source_barrier_saturation.py').Experiment(base)
    jobs, count = previous.prepare_jobs(source, engine)
    require(encode(count) == old['count_law'], 'The unchanged original AP count law and complete infinite tail')
    require(len(old['results']) == 15, 'Exactly four AP11 and eleven existing linear bounds')
    rows = []
    for job, original in zip(jobs[:4], old['results'][:4]):
        require(job['kind'] == original['kind'] == 'AP11'
                and job['name'] == original['name']
                and encode(job['coefficients']) == original['coefficients'] == original['scan']['coefficients']
                and F(original['at_one']) == job['at_one'] == 0,
                'The identical complete original AP11 block objective')
        scan_input = dict(original)
        scan_input['index'] = original['name']
        scan = problem.scan(scan_input)
        value = scan['complete_hinge_upper']
        old_upper = F(original['adopted_upper'])
        mean = sum(job['coefficients'].values())*(MEAN-MASS)
        adopted = min(value, old_upper, mean)
        require(0 < adopted < old_upper and value == adopted,
                'Each complete joint AP11 block strictly improves its original bound')
        rows.append({'name': job['name'], 'kind': 'AP11', 'block': job['block'],
                     'coefficients': job['coefficients'], 'at_one': F(0), 'scan': scan,
                     'complete_head_upper': value, 'previous_adopted_upper': old_upper,
                     'complete_mean_only_upper': mean, 'adopted_upper': adopted,
                     'improvement_over_previous': old_upper-adopted})
    require([row['name'] for row in rows] == ['AP11-'+str(i) for i in range(4)]
            and problem.used == set(problem.bank), 'All four original blocks and every retained dual are consumed')
    AP13 = next(row for row in prior['results'] if row['index'] == 'AP13')
    U4 = F(AP13['adopted_upper'])
    require(U4 == F(22263628571451221, 113400000000000000), 'The same complete244 independent AP13 input')
    tail = count['remaining_hinge1_coefficient']*(MEAN-MASS)+count['whole_constant_coefficient']*MASS
    total = sum(row['adopted_upper'] for row in rows)
    previous_total = sum(row['previous_adopted_upper'] for row in rows)
    denominator = MASS-U4/6-(total+tail)/7
    old_denominator = MASS-U4/6-(previous_total+tail)/7
    require(tail == F(old['complete_count_tail_upper']) == F(277, 4392300)
            and total < previous_total and 0 < old_denominator < denominator
            and denominator-old_denominator == (previous_total-total)/7,
            'The complete survival denominator improves with identical AP13, mass and infinite count tail')
    return encode({'schema': 'erdos7-j-face-joint-survival-heads-v1', 'source_sha256': pins,
        'geometry': old['geometry'], 'source_mass': F(1, 4), 'survivor_mass': MASS,
        'complete_mean_upper': MEAN, 'model': problem.specification, 'count_law': count,
        'results': rows, 'rational_duals': {key: problem.bank[key] for key in sorted(problem.used)},
        'distinct_dual_count': len(problem.used), 'rational_column_checks': 876*len(problem.used),
        'total_containing_choices': sum(row['scan']['covered_containing_choices'] for row in rows),
        'total_independent_affine_checks': sum(row['scan']['independent_affine_checks'] for row in rows),
        'inherited_AP13_upper': U4, 'complete_count_tail_upper': tail,
        'complete_AP11_sum_upper': total, 'previous_AP11_sum_upper': previous_total,
        'uniform_denominator_lower': denominator, 'previous_denominator_same_AP13': old_denominator,
        'complete_denominator_improvement': denominator-old_denominator,
        'scope': 'All four complete original AP11 blocks on both entire actual saturated J faces. The unchanged244 joint876-variable source model retains all selected original labels, ten marked residual constraints, one common late split and complete exponent tails. Each block covers6250000 containing choices. The complete survival denominator uses the existing244 AP13, exact mass3/20, mean16/25 and the whole AP count tail. No new52-cost numerator/global comparison, off-face extension, actual LP attainment, Lean verification or unrestricted Erdos7 resolution is asserted.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--proposal', type=Path)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(args.proposal is None or args.write, 'A proposal is consumed only by the writer')
    require(not args.write or args.proposal is not None, 'The writer needs exact proposed duals')
    io = module('j_ap_joint_reader', args.base/'certificate_io.py')
    joint = module('j_ap_joint_json', args.base/'frontier/j-source/j_face_joint_selected_heads.py')
    record = json.loads(io.read_artifact_bytes(args.proposal if args.write else args.base/CERTIFICATE),
                        object_pairs_hook=joint.unique)
    result = calculate(args.base, record['rational_duals'])
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        require(result == record, 'Every complete J AP11 block and survival certificate field recomputes exactly')
    print('PASS:4 complete AP11 blocks,25000000 containing choices,'+str(result['distinct_dual_count'])
          +' exact876-column duals and the complete positive survival denominator.', flush=True)


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
