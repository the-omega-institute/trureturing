#!/usr/bin/env python3
"""Use one raw-source LP for four independent AP11 blocks and AP13."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/joint_selected_survival_comparison.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/transport/joint_selected_source_comparison.py': 'ab18c0c4ac40af60f7c974393d82738ec4d762ccefa7f5efe61cf4b963b3673c',
    'certificates/source_norms/joint_selected_source_comparison.json': '81ca26366a56753ff9a84c002c97ed9f4a0f2317fb6e2a858c25774c3283b07e',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable complete source')
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


def flatten_dual_buckets(buckets):
    result = {}
    for prefix, records in buckets.items():
        require(len(prefix) == 1 and prefix in '0123456789abcdef', 'Canonical dual hash bucket')
        for key, record in records.items():
            require(len(key) == 64 and key.startswith(prefix) and key not in result, 'Unique bucketed dual hash')
            result[key] = record
    return result


def calculate(base, bank=None, proposer=None):
    io = module('joint_survival_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    prior, quadratic, laws, identities_cert = map(read, ('joint_selected_source_comparison',
        'expanded_seven_quadratic_comparison', 'expanded_seven_survival_comparison', 'load_two_cost_remainders'))
    pins = dict(PINS)
    for data in (prior, quadratic, laws, identities_cert):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent inherited source '+path)
            pins[path] = pin
    require(all(path in pins for path in ('certificates/source_norms/expanded_seven_quadratic_comparison.json',
        'certificates/source_norms/expanded_seven_survival_comparison.json',
        'certificates/source_norms/load_two_cost_remainders.json')), 'Every direct certificate is pinned')
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('joint_survival_'+name, base/'frontier'/(name+'.py'))
    original = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == pin for path, pin in original.pins.items()), 'Complete original52-cost inventory')
    D, L, Q = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(8201, 1800))
            and all(data['faces'] == prior['faces'] and data['r'] == data['rho'] == '0'
                    and F(data['mass']) == D for data in (prior, quadratic, laws, identities_cert)),
            'One actual source domain and both whole saturated K faces')

    count = module('joint_survival_count_law', base/'verify_joint_frontier.py')
    probabilities = {n: count.ap_count_probability(11, F(5, 3), n) for n in range(1, 5)}
    identities = {1: {5: F(1)}, 2: {2: F(1), 3: F(1)},
                  3: {1: F(1), 2: F(2)}, 4: {1: F(3), 2: F(1)}}
    tail0, tail1 = tuple(F(50, 3)*v for v in count.geom(11, 5)[:2])
    require(encode(probabilities) == laws['count_probabilities'] and encode(identities) == laws['all_load_identities']
            and (tail0, tail1) == (F(5, 43923), F(17, 29282))
            and sum(probabilities.values())+tail0 == 1
            and sum(n*p for n, p in probabilities.items())+tail1 == F(7, 6),
            'Every original count probability and the full infinite first moment')
    for n, cs in identities.items():
        require(min(cs.values()) > 0 and sum(cs.values()) == n and sum(t*c for t, c in cs.items()) == 5
                and all(sum(c*max(v-t, 0) for t, c in cs.items()) == max(n*v-5, 0)
                        for v in range(1, 7)), 'Every finite transition and entire original affine count identity')
    tail = prior['full_count_tail']
    require(tail == laws['full_count_tail'] == quadratic['full_count_tail']
            and F(tail['probability']) == tail0 and F(tail['first_moment']) == tail1
            and F(tail['remaining_hinge1_coefficient']) == tail1-4*tail0
            and F(tail['whole_constant_coefficient']) == tail1-5*tail0
            and F(tail['remaining_cost_upper']) == (tail1-4*tail0)*(L-D)+(tail1-5*tail0)*D
            == F(3337, 52707600), 'All remaining blocks and every infinite-count constant retained')

    problem = load('transport/joint_selected_source_comparison').JointSelectedHead(base, bank, proposer)
    old_blocks = prior['AP11_block_results']
    require(len(old_blocks) == 4, 'Four original AP11 tests retain their separate indices')
    records = []
    for e, old in enumerate(old_blocks):
        coefficients = {t: sum(probabilities[n]*identities[n].get(t, 0)/n for n in range(e+1, 5))
                        +(tail0 if t == 1 else 0) for t in (1, 2, 3, 5)}
        coefficients = {t: c for t, c in coefficients.items() if c}
        old_co = {int(t): F(c) for t, c in old['hinge_coefficients'].items() if F(c)}
        require(coefficients == old_co and old['block'] == e,
                'One original block test throughout all its original count outcomes')
        scan = problem.scan(coefficients)
        previous = F(old['joint_mean_upper'])
        bound = min(previous, scan['complete_hinge_upper'])
        records.append({'block': e, 'hinge_coefficients': coefficients, 'previous_upper': previous,
            'joint_mean_upper': bound, 'denominator_gain': (previous-bound)/7, 'scan': scan})
        print('Checked independent AP11 block'+str(e)+': '+str(float(bound))+', '
              +str(scan['counts']['joint'])+' exact dual uses.', flush=True)
    scan13 = problem.scan({4: F(1)})
    oldU4 = F(prior['uniform_hinge4_upper'])
    require(oldU4 == 6*F(prior['standalone_hinge4_penalty']) == F(295741, 1543500),
            'The unchanged full209 separate AP13 comparison')
    U4 = min(oldU4, scan13['complete_hinge_upper'])
    require(U4 < oldU4 and records[0]['joint_mean_upper'] < F(old_blocks[0]['joint_mean_upper']),
            'Both block zero and the uniform fourth hinge improve strictly')
    ap13 = {'hinge_coefficients': {4: F(1)}, 'previous_upper': oldU4, 'hinge_upper': U4,
            'denominator_gain': (oldU4-U4)/6, 'scan': scan13}
    denominator = D-U4/6-(sum(r['joint_mean_upper'] for r in records)+F(tail['remaining_cost_upper']))/7
    old_denominator = D-oldU4/6-(sum(F(r['joint_mean_upper']) for r in old_blocks)
        +F(tail['remaining_cost_upper']))/7
    gain = sum(r['denominator_gain'] for r in records)+ap13['denominator_gain']
    require(old_denominator == F(prior['uniform_denominator_lower'])
            and denominator == old_denominator+gain > old_denominator > 0,
            'Exactly four independent AP11 gains plus the independent AP13 gain')

    tags = [s['tag'] for s in original.specs+original.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(encode(tags) == prior['original_cost_tags'] and prior['all_original_indices'] == list(range(52))
            and len(tags) == len(old_costs) == len(weights) == 52 and min(weights) > 0,
            'Every complete209 original function, independent test and positive weight retained')
    require(tags[48] == ('s', F(9)), 'Uniform raw-square9 is exactly original cost48')
    U9, T5 = old_costs[48], F(quadratic['second_factorial_tail_upper'])
    require(U9 == F(quadratic['uniform_raw_square9_upper']) == F(17859883, 4630500)
            and T5 == F(2303, 2700), 'Complete207 uniform raw-square and factorial bounds retained')
    direct, feedback = list(old_costs), []
    remainders = load('transport/load_two_cost_remainders')
    for row in remainders.SUPPORTS:
        i = row[0]
        identity = remainders.verify_identity(original.source, tags[i], row)
        saved = [r for r in identities_cert['exact_integer_identities'] if r['index'] == i]
        require(len(saved) == 1 and all(saved[0][k] == encode(v) for k, v in identity.items()),
                'The original202 identity is exact at every positive integer load')
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
            'No signed actual mass, complete square or preceding cost is lost')
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(oldN == F(prior['numerator_upper']) > N > 0
            and offset+oldN/old_denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']),
            'One complete stronger numerator and denominator, without adding separate savings twice')
    if proposer is None:
        require(set(problem.bank) == problem.used, 'Every retained rational dual is used and verified')
    retained_bank = {}
    for key in sorted(problem.used):
        retained_bank.setdefault(key[0], {})[key] = problem.bank[key]
    return encode({'schema': 'erdos7-joint-selected-survival-comparison-v1', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'raw_lp': problem.lp.specification(), 'rational_dual_buckets': retained_bank,
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
        'joint_dual_uses': sum(r['scan']['counts']['joint'] for r in records)+scan13['counts']['joint'],
        'scope': 'Four original AP11 block tests and the independent AP13 hinge each use209 complete common raw-source LP, with all original residues and both seven depths. The uniform h4 result also feeds202 exact identities on each separate numerator test. Every original count tail,52 costs, signed mass and complete square remains on both whole saturated actual K faces. No shared optimizer across tests, positive load-two mass, actual attainment, off-face/global extension, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('joint_survival_reader', args.base/'certificate_io.py')
    expected = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
    result = calculate(args.base, flatten_dual_buckets(expected['rational_dual_buckets']))
    require(result == expected, 'Exact complete common-source survival certificate')
    print('PASS: five complete independent survival tests, all52 costs and face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
