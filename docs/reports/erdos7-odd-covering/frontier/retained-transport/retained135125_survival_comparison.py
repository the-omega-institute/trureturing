#!/usr/bin/env python3
"""Retain joint original135/125 states in two complete survival tests and their52-cost consumer."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/retained-transport/retained135125_survival_comparison.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/retained-transport/retained135125_heavy_comparison.py': '06fa084b5ce23b8abd6119e8e767ab648c06b183690fe6c60f9d8d20788c58e2',
    'certificates/source_norms/retained-transport/retained135125_heavy_comparison.json': '451537f6ee699920c955ba0401cedba672f0aaabc97ad193cb282163bcfaf6cf',
    'frontier/retained-transport/retained135_heavy_comparison.py': '93ad67489e6ce429f45bd8888cfd8f6e5ac91b0bc3d4fbeebfedef9f7d4b84ac',
    'frontier/retained-transport/retained135_survival_comparison.py': 'd89258d6ff710ae6479c1e4e5530ef2e81465c7bed9876d94c7bbdaa1c4a5350',
    'certificates/source_norms/retained-transport/retained135_survival_comparison.json': '6a203d7da0717fd8b16d3a8016375ea80bdc5848c68753fa72c8690da8a7f176',
    'frontier/comparison-bounds/load_two_cost_remainders.py': '4bb1f09f0768f92b9dc447156ad0c816e1858c7a1e553c2b422ebe878d7d0ec2',
    'certificates/source_norms/comparison-bounds/load_two_cost_remainders.json': 'f4224aa378cf67701c4d67bc6e7781277163ad429970727013673aa4e3b2a9e3',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable complete original source')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def calculate(base, bank=None, proposer=None):
    io = module('retained135125_survival_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, laws, identities_cert = map(read, ('retained135125_heavy_comparison',
        'retained135_survival_comparison', 'load_two_cost_remainders'))
    pins = dict(PINS)
    for data in (prior, laws, identities_cert):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent complete predecessor '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical source '+path)
    load = lambda name: module('retained135125_survival_'+name, io.named_artifact(base/'frontier', name+'.py'))
    original = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in original.pins.items()), 'Complete original52-cost inventory')
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and all(data['faces'] == prior['faces'] and data['r'] == data['rho'] == '0'
                    and F(data['mass']) == D for data in (prior, laws, identities_cert)),
            'The same two complete actual saturated K faces and common residual')

    count = module('retained135125_survival_count', base/'verify_joint_frontier.py')
    probabilities = {n: count.ap_count_probability(11, F(5, 3), n) for n in range(1, 5)}
    identities = {1: {5: F(1)}, 2: {2: F(1), 3: F(1)},
                  3: {1: F(1), 2: F(2)}, 4: {1: F(3), 2: F(1)}}
    tail0, tail1 = tuple(F(50, 3)*v for v in count.geom(11, 5)[:2])
    require(encode(probabilities) == laws['count_probabilities'] and encode(identities) == laws['all_load_identities']
            and (tail0, tail1) == (F(5, 43923), F(17, 29282))
            and sum(probabilities.values())+tail0 == 1
            and sum(n*p for n, p in probabilities.items())+tail1 == F(7, 6),
            'All original count probabilities and the complete infinite first moment')
    for n, cs in identities.items():
        require(min(cs.values()) > 0 and sum(cs.values()) == n and sum(t*c for t, c in cs.items()) == 5
                and all(sum(c*max(v-t, 0) for t, c in cs.items()) == max(n*v-5, 0)
                        for v in range(1, 7)), 'Finite count transitions and the entire original affine tails')
    tail = prior['full_count_tail']
    require(tail == laws['full_count_tail'] and F(tail['probability']) == tail0
            and F(tail['first_moment']) == tail1
            and F(tail['remaining_hinge1_coefficient']) == tail1-4*tail0
            and F(tail['whole_constant_coefficient']) == tail1-5*tail0
            and F(tail['remaining_cost_upper']) == (tail1-4*tail0)*(L-D)+(tail1-5*tail0)*D
            == F(3337, 52707600), 'Every omitted count block and its full infinite constant retained')

    retained = load('retained135125_heavy_comparison')
    problem = retained.retained_pair_head_class(base)(base, bank, proposer)
    old_blocks = prior['AP11_block_results']
    require(old_blocks == laws['AP11_block_results'] and len(old_blocks) == 4
            and [row['block'] for row in old_blocks] == list(range(4)),
            'Four independent original AP11 block labels')
    oldU4 = F(prior['uniform_hinge4_upper'])
    require(oldU4 == 6*F(prior['standalone_hinge4_penalty']) == F(prior['AP13_result']['hinge_upper'])
            == F(laws['uniform_hinge4_upper']), 'The complete inherited AP13 comparison')
    print('Scanning independent AP13 over62,500,000 original choices.', flush=True)
    scan13 = problem.scan({4: F(1)})
    U4 = min(oldU4, scan13['complete_hinge_upper'])
    ap13 = {'hinge_coefficients': {4: F(1)}, 'previous_upper': oldU4, 'hinge_upper': U4,
            'denominator_gain': (oldU4-U4)/6, 'scan': scan13}
    coefficients = {t: sum(probabilities[n]*identities[n].get(t, 0)/n for n in range(1, 5))
                    +(tail0 if t == 1 else 0) for t in (1, 2, 3, 5)}
    coefficients = {t: c for t, c in coefficients.items() if c}
    require(encode(coefficients) == old_blocks[0]['hinge_coefficients'], 'One complete original AP11 first-block function')
    print('Scanning independent AP11 block0 over62,500,000 original choices.', flush=True)
    scan0 = problem.scan(coefficients)
    old0 = F(old_blocks[0]['joint_mean_upper'])
    bound0 = min(old0, scan0['complete_hinge_upper'])
    records = [{'block': 0, 'hinge_coefficients': coefficients, 'previous_upper': old0,
                'joint_mean_upper': bound0, 'denominator_gain': (old0-bound0)/7, 'scan': scan0}]+old_blocks[1:]
    require(U4 < oldU4 and bound0 < old0 and encode(records[1:]) == prior['AP11_block_results'][1:],
            'Both complete scanned tests improve and the other three AP11 tests remain unchanged')
    denominator = D-U4/6-(sum(F(r['joint_mean_upper']) for r in records)+F(tail['remaining_cost_upper']))/7
    old_denominator = D-oldU4/6-(sum(F(r['joint_mean_upper']) for r in old_blocks)
                              +F(tail['remaining_cost_upper']))/7
    gain = (oldU4-U4)/6+(old0-bound0)/7
    require(old_denominator == F(prior['uniform_denominator_lower']) > 0
            and denominator == old_denominator+gain > old_denominator,
            'Exactly two independent survival gains and every complete denominator term')

    tags = [s['tag'] for s in original.specs+original.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(encode(tags) == prior['original_cost_tags'] and prior['all_original_indices'] == list(range(52))
            and len(tags) == len(old_costs) == len(weights) == 52 and min(weights) > 0,
            'All225 original independent numerator labels and their positive weights')
    U9, T5 = old_costs[48], F(laws['second_factorial_tail_upper'])
    require(tags[48] == ('s', F(9)) and U9 == F(laws['uniform_raw_square9_upper']) == F(17859883, 4630500)
            and T5 == F(2303, 2700), 'Complete inherited square9 and factorial5 bounds')
    direct, feedback = list(old_costs), []
    remainders = load('load_two_cost_remainders')
    for row in remainders.SUPPORTS:
        i = row[0]
        identity = remainders.verify_identity(original.source, tags[i], row)
        saved = [r for r in identities_cert['exact_integer_identities'] if r['index'] == i]
        require(len(saved) == 1 and all(saved[0][k] == encode(v) for k, v in identity.items()),
                'The original202 identity including its complete polynomial tail')
        bound = (identity['square_minus_mass']*(Q-D)+identity['raw_square9']*U9
                 +identity['hinge4']*U4+identity['factorial5']*T5)
        before = direct[i]
        direct[i] = min(before, bound)
        feedback.append({**identity, 'previous_cost_upper': before, 'source_bound': bound,
            'accepted_cost_upper': direct[i], 'weighted_gain': weights[i]*(before-direct[i])})
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda n, tag=t: original.source.zero5_cost(tag, n) for t in all_tags]
    metadata = [original.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    require(signed < 0 < square_weight and all(0 <= b <= a for a, b in zip(old_costs, costs)),
            'Signed actual mass, complete square and every preceding original cost retained')
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(oldN == F(prior['numerator_upper']) >= N > 0
            and offset+oldN/old_denominator == F(prior['comparison_upper'])
            and comparison < F(prior['comparison_upper']), 'One complete stronger52-cost ratio')
    if proposer is None:
        require(set(problem.bank) == problem.used, 'Every stored exact branch dual is used and checked')
    duals = {key: problem.bank[key] for key in sorted(problem.used)}
    return encode({'schema': 'erdos7-retained135125-survival-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'branch_lps': {branch: lp.specification() for branch, lp in problem.branch_lps.items()},
        'rational_duals': load('retained135_heavy_comparison').encode_dual_bank(duals, retained.NROWS, retained.NEQ), 'selected_policy': prior['selected_policy'],
        'newly_scanned_survival_tests': ['AP13', 'AP11-block0'], 'inherited_AP11_blocks': [1, 2, 3],
        'count_probabilities': probabilities, 'all_load_identities': identities,
        'AP11_block_results': records, 'AP13_result': ap13, 'full_count_tail': tail,
        'standalone_hinge4_penalty': U4/6, 'uniform_hinge4_upper': U4,
        'uniform_raw_square9_upper': U9, 'second_factorial_tail_upper': T5,
        'previous_denominator_lower': old_denominator, 'uniform_denominator_gain': gain,
        'uniform_denominator_lower': denominator, 'integer_identity_feedback': feedback,
        'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
        'previous_cost_bounds': old_costs, 'direct_cost_bounds': direct, 'improved_cost_bounds': costs,
        'majorants': majorants, 'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
        'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
        'previous_numerator_upper': oldN, 'numerator_upper': N, 'numerator_improvement': oldN-N,
        'offset': offset, 'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
        'comparison_improvement': F(prior['comparison_upper'])-comparison,
        'previous_prefix_duals_used': sorted(problem.prior_used),
        'joint_dual_uses': scan13['counts']['joint']+scan0['counts']['joint'],
        'scope': 'Two independent complete survival tests, AP13 and AP11 block0, use225 common raw-source, actual-survivor and joint135/125 LP, each over62,500,000 original containing choices and both27/81 branches. AP11 blocks1,2,3 retain218 bounds without new scans. All3705 dual columns, the full count tail, all52 independent original costs, negative actual mass and the complete square remain. The uniform h4 bound feeds202 exact identities separately for each original cost. No shared optimizer, positive load-two mass, actual-family attainment, off-face/global extension, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('retained135125_survival_reader', args.base/'certificate_io.py')
    expected = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
    retained = module('retained135125_survival_codec', args.base/'frontier/retained-transport/retained135125_heavy_comparison.py')
    exact = module('retained135125_survival_exact', args.base/'frontier/retained-transport/retained135_heavy_comparison.py')
    result = calculate(args.base, exact.decode_dual_bank(expected['rational_duals'], retained.NROWS, retained.NEQ))
    require(result == expected, 'Exact complete retained135/125 survival certificate')
    print('PASS: two complete survival scans, all3705 dual columns and52-cost face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
