#!/usr/bin/env python3
"""Two disjoint complete prime-path square blocks retain the original J head."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j-source/j_face_pure_path_square.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/j-source/j_face_joint_retained_square.py': '201c771c42af3f979eb6271152285ca2c250430a42de3ea7122d0f5c383b58a8', 'certificates/source_norms/j-source/j_face_joint_retained_square.json': 'f99a644a80049cd10278e27000b486927a96a0bf9c22c08c9da4f6c9a8081c4d', 'profile-notes/j-source/245-the-actual-j-survivor-mass-and-h-column-sharpen-the-complete-square.md': 'f2623f36d5ffbf88014517bfb77fce964e2b603ed8711333a6823412f275b4ef', 'frontier/j-source/j_face_pure_path_factorial.py': 'b0888d8b5094782439a113b9a04d936dfcf6df4ce1190e8a0e9e6aa254631930', 'certificates/source_norms/j-source/j_face_pure_path_factorial.json': '119ea1549bd3edff0ecad0f74859660dff68ee64cd995c3d49583ceb2a70dd59', 'profile-notes/j-source/248-the-complete-j-factorial-tail-retains-both-prime-paths.md': '295efbd2439d70186636cf8943f0c6253bc02f0fcf506a2296163b62614252ef'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original mathematical provider')
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


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Unique certificate key: '+key)
        result[key] = value
    return result


def square_path(prime, start, cross, caps, ordered_pair_charge):
    """The complete 2BR+R^2 block, including its single-label diagonals."""
    r, initial = F(1, prime), F(1, prime**start)
    diagonal_weight = initial/(1-r)
    twice_distinct_weight = 2*initial*r/(1-r)**2
    old_cross = 2*max(cross)*diagonal_weight
    old_diagonal = max(caps)*diagonal_weight
    require(ordered_pair_charge == max(caps)*twice_distinct_weight,
            'The exact old complete ordered distinct-pair subseries')
    records = []
    for a, c in zip(cross, caps):
        require(a >= 0 and c >= 0, 'Nonnegative original head and survivor coefficients')
        reward0, reward_step = 2*a+c, 2*c
        potential0 = reward0/(1-r)+reward_step*r/(1-r)**2
        potential_step = reward_step/(1-r)
        constant_identity = reward0+r*(potential0+potential_step)-potential0
        count_identity = reward_step+r*potential_step-potential_step
        reward_slack = (1-r)*potential0-reward0
        require(constant_identity == count_identity == 0 and reward_slack >= 0,
                'Bellman affine identity for every count and domination of unchanged components')
        upper = initial*potential0
        expected = (a+c)/9 if prime == 3 else a/10+3*c/40
        require(upper == expected, 'Complete depth-start square-path geometric sum')
        records.append({'cross_coefficient': a, 'density_cap': c, 'reward_constant': reward0,
                        'reward_count_coefficient': reward_step, 'potential_constant': potential0,
                        'potential_count_coefficient': potential_step,
                        'bellman_constant_identity': constant_identity,
                        'bellman_count_identity': count_identity,
                        'unchanged_component_reward_slack': reward_slack, 'complete_path_upper': upper})
    new = max(row['complete_path_upper'] for row in records)
    old = old_cross+old_diagonal+ordered_pair_charge
    require(new <= old and min(old_cross, old_diagonal, ordered_pair_charge) >= 0,
            'Replace precisely one complete nonnegative square block')
    return {'prime': prime, 'first_depth': start, 'discount': r, 'initial_weight': initial,
            'diagonal_geometric_weight': diagonal_weight,
            'ordered_distinct_geometric_weight': twice_distinct_weight,
            'old_twice_head_cross': old_cross, 'old_diagonal': old_diagonal,
            'old_ordered_distinct_pairs': ordered_pair_charge,
            'old_complete_block': old, 'path_records': records,
            'maximizing_cells_or_slots': [i for i,row in enumerate(records) if row['complete_path_upper'] == new],
            'new_complete_block': new, 'block_change': new-old}


def calculate(base):
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned canonical certificate reader')
    io = module('j_path_square_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')),
                                   object_pairs_hook=unique)
    prior, paths = read('j-source/j_face_joint_retained_square'), read('j-source/j_face_pure_path_factorial')
    pins = dict(PINS)
    for record in (prior, paths):
        for path, pin in record['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent complete source input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned mathematical input '+path)
    require(prior['geometry'] == paths['geometry']
            and F(prior['survivor_mass']) == F(paths['survivor_mass']) == F(3,20)
            and F(prior['complete_mean_upper']) == F(paths['complete_mean_upper']) == F(16,25),
            'Both complete actual saturated J faces and the same unnormalized survivor')
    j = module('j_path_square_source', base/'frontier/j-source/j_face_coupled_seven_heads.py')
    moment = module('j_path_square_moment', base/'frontier/j-source/j_face_shared_square_factorial.py')
    joint = module('j_path_square_joint', base/'frontier/j-source/j_face_joint_retained_square.py')
    path_provider = module('j_path_square_caps', base/'frontier/j-source/j_face_pure_path_factorial.py')
    factorial = module('j_path_square_tail', base/'frontier/complete_off_face_factorial_tail.py')
    require(tuple(map(F, prior['geometry']['late_split_interval'])) == (j.LO,j.HI),
            'One common complete late-parameter interval')
    tail = moment.complete_tail(factorial)
    require(encode(tail) == prior['complete_tail_partition'] == paths['complete_tail_partition'],
            'The entire241 tail with both diagonals and every old/seven pair')
    c3, c5 = tuple(map(F,paths['pure3_cell_density_caps'])),tuple(map(F,paths['pure5_slot_density_caps']))
    require(c3 == path_provider.C3 == (F(11,20),F(2,5),F(1,5),F(2,5),F(2,5))
            and c5 == path_provider.C5 == (F(0),F(1,10),F(29,90),F(13,30),F(4,15)),
            'The complete248 original cell and slot density caps')
    controller = tuple(prior['controller_layout'])
    require(controller == joint.CONTROLLER == (1,4,2,1,2,4,2), 'The original sole245 controller')
    problem, lp = moment.JMomentHead(j),joint.JointSurvivorLP(j)
    B = joint.head_load(j,controller)
    dual = lp.check_dual(B)
    require(encode(lp.specification()) == prior['joint_source_model']
            and encode(dual) == prior['exact_retained_head_dual'],
            'The unchanged101-column joint head model and exact2593/1800 dual')
    old_components = joint.old_complete_bound(j,problem,controller,tail['complete_ordered_tail_square'])
    require(encode(old_components) == prior['controller_original_components'],
            'Recomputed complete old controller at both common-theta endpoints')
    wB = tuple(a*b for a,b in zip(problem.w,B))
    A3 = tuple(sum(problem.pre[5*c+s]*wB[5*c+s] for s in range(5)) for c in range(5))
    A5 = tuple(sum(problem.descendant[5*c+s]*wB[5*c+s] for c in range(5)) for s in range(5))
    require(A3 == tuple(map(F,('18/25','53/100','11/25','31/25','93/50')))
            and A5 == tuple(map(F,('0','1/9','4/3','8/9','49/90'))),
            'Both crosses use the same original B and the original normalized/absolute tables')
    block3 = square_path(3,3,A3,c3,tail['weighted_old_pure_before_halving']['pure3'])
    block5 = square_path(5,2,A5,c5,tail['weighted_old_pure_before_halving']['pure5'])
    blocks = (block3,block5)
    old_cross_remaining = old_components['twice_old_cross']-sum(b['old_twice_head_cross'] for b in blocks)
    old_diagonal_remaining = tail['old_diagonal']-sum(b['old_diagonal'] for b in blocks)
    ordered_distinct_remaining = 2*tail['distinct_tail_pairs']-sum(b['old_ordered_distinct_pairs'] for b in blocks)
    tail_remaining = old_diagonal_remaining+ordered_distinct_remaining+tail['positive7_diagonal']
    require(min(old_cross_remaining,old_diagonal_remaining,ordered_distinct_remaining) >= 0
            and tail_remaining == tail['complete_ordered_tail_square']
                -sum(b['old_diagonal']+b['old_ordered_distinct_pairs'] for b in blocks),
            'Remove only the two complete pure-prime self blocks; all mixed pairs and seven diagonals remain')
    delta = sum(b['block_change'] for b in blocks)
    require((block3['block_change'],block5['block_change'],delta) == (F(-1,60),F(-1,120),F(-1,40)),
            'Exact independent disjoint block savings')
    endpoints = []
    for theta,cross_tail in zip((j.LO,j.HI),old_components['complete_cross_tail_endpoint_uppers']):
        seven_cross = F(2,5)*problem.raw_row(B,theta)
        direct = dual['head_square_upper']+old_cross_remaining+seven_cross+tail_remaining
        direct += sum(b['new_complete_block'] for b in blocks)
        require(direct == dual['head_square_upper']+cross_tail+delta,
                'Full square partition equals old controller with each block replaced exactly once')
        endpoints.append({'theta':theta,'old_complete_cross_tail':cross_tail,
                          'unchanged_twice_positive7_cross':seven_cross,'new_complete_upper':direct})
    old_controller = dual['head_square_upper']+max(old_components['complete_cross_tail_endpoint_uppers'])
    controller_upper = max(row['new_complete_upper'] for row in endpoints)
    require(old_controller == F(prior['complete_square_upper']) == F(prior['controller_complete_upper']) == F(5539,1200)
            and controller_upper == F(5509,1200), 'Exact old and new complete controller bounds')
    # The already checked245 theorem supplies the entire complementary layout
    # maximum. This consumer pins its code, certificate and full input closure;
    # it does not claim to rerun that original12500-layout scan.
    other = F(prior['other_head_maximum'])
    require(prior['original_head_count'] == 12500 and prior['joint_dual_head_count'] == 1
            and prior['other_complete_head_count'] == 12499 and other == F(16439,3600)
            and other < controller_upper and prior['other_maximizing_witnesses']
            and len(prior['all_complete_head_components_sha256']) == 64,
            'Direct reuse of245 complete complementary-layout theorem below the new controller')
    final = max(other,controller_upper)
    require(final == F(5509,1200) and old_controller-final == F(1,40)
            and F(paths['complete_factorial_upper']) == F(6313,7200), 'Complete improved square and directly inherited factorial')
    return encode({'schema':'erdos7-j-face-pure-path-square-v1','source_sha256':pins,
        'geometry':prior['geometry'],'survivor_mass':F(3,20),'complete_mean_upper':F(16,25),
        'complete_square_upper':final,'previous_complete_square_upper':old_controller,
        'complete_square_improvement':old_controller-final,'complete_factorial_upper':F(paths['complete_factorial_upper']),
        'controller_layout':controller,'controller_head_values':B,'exact_retained_head_dual':dual,
        'joint_source_model':lp.specification(),'pure3_cell_density_caps':c3,'pure5_slot_density_caps':c5,
        'pure3_square_block':block3,'pure5_square_block':block5,
        'complete_original_tail_partition':tail,'unchanged_twice_other_old_cross':old_cross_remaining,
        'unchanged_old_diagonal':old_diagonal_remaining,'unchanged_ordered_distinct_pairs':ordered_distinct_remaining,
        'unchanged_positive7_diagonal':tail['positive7_diagonal'],'complete_remaining_tail_square':tail_remaining,
        'controller_endpoint_records':endpoints,'controller_complete_upper':controller_upper,
        'original_head_count':12500,'recomputed_controller_count':1,
        'inherited_other_complete_head_count':12499,'other_head_maximum':other,
        'other_head_gap_to_new_upper':final-other,
        'inherited245_all_head_components_sha256':prior['all_complete_head_components_sha256'],
        'scope':'Both entire actual saturated J faces and the common full late interval. One original controller retains its exact245 joint2593/1800 survivor head; two disjoint complete2BR+R^2 blocks use248 original prime-path caps and include diagonals once. All other mixed, root/cell-five and positive-seven terms remain. The pinned245 all-layout theorem supplies the other12499 layouts without rerunning its scan. Factorial6313/7200 is directly inherited from248. No actual attainment, off-face or full52-cost comparison, Lean verification or unrestricted Erdos7 result.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write',action='store_true')
    modes.add_argument('--check',action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('j_path_square_writer',args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE,json.dumps(result,indent=2)+'\n')
    else:
        require(result == json.loads(io.read_artifact_bytes(args.base/CERTIFICATE),object_pairs_hook=unique),
                'Every exact complete J path-square certificate field recomputes')
    print('PASS:complete J square='+result['complete_square_upper']+'; gain='+result['complete_square_improvement']
          +'; exact101-column head and both complete prime-path square blocks.')


if __name__ == '__main__':
    try:
        main()
    except(ValueError,ArithmeticError,OSError,KeyError,TypeError,json.JSONDecodeError) as error:
        print('FAIL: '+str(error),file=sys.stderr)
        raise SystemExit(1)
