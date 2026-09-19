#!/usr/bin/env python3
"""Retain all four selected labels in survival and eleven original linear costs."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/all_selected_survival_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/source-budgets/all_selected_heavy_comparison.py': '88e121a2b88e7f0abbf83e848c4b02581bfa7443f85c136f7589be8a2b9c3e11', 'certificates/source_norms/source-budgets/all_selected_heavy_comparison.json': '48ae436cbbf439efd7db0110ce93ac28e40a833392d64eb06dc78de7511d6a9e'}


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


def encode_dual_bank(bank):
    """Intern exact rationals; keep all 132+4 dual entries and the bound."""
    values = sorted({'0'} | {v for record in bank.values()
        for v in list(record['nonzero_inequality_duals'].values())
        +record['equality_duals']+[record['raw_objective_upper']]})
    indices = {value: str(i) for i, value in enumerate(values)}
    buckets = {}
    for key in sorted(bank):
        record = bank[key]
        entries = [record['nonzero_inequality_duals'].get(str(i), '0') for i in range(132)]
        entries += record['equality_duals']+[record['raw_objective_upper']]
        require(len(entries) == 137, 'Complete exact dual dimensions')
        buckets.setdefault(key[0], {}).setdefault(key[1], {})[key] = ','.join(indices[v] for v in entries)
    return {'codec': 'exact-rational-table-dense-duals-v1',
            'inequality_count': 132, 'equality_count': 4,
            'rational_table': [' '.join(values[i:i+128]) for i in range(0, len(values), 128)],
            'dual_buckets': buckets}


def decode_dual_bank(encoded):
    """Decode independently; feasibility is still checked in every LP column."""
    require(isinstance(encoded, dict) and set(encoded) == {'codec', 'inequality_count',
        'equality_count', 'rational_table', 'dual_buckets'}, 'Exact dual codec fields')
    require(encoded['codec'] == 'exact-rational-table-dense-duals-v1'
            and type(encoded['inequality_count']) is int and encoded['inequality_count'] == 132
            and type(encoded['equality_count']) is int and encoded['equality_count'] == 4,
            'Exact dual codec and complete dimensions')
    table = encoded['rational_table']
    require(isinstance(table, list) and table and all(isinstance(row, str) for row in table),
            'Nonempty exact rational table')
    pieces = [row.split(' ') for row in table]
    require(all(len(row) == 128 for row in pieces[:-1]) and 1 <= len(pieces[-1]) <= 128,
            'Canonical rational-table blocks')
    values = [value for row in pieces for value in row]
    require(values == sorted(set(values)) and '0' in values
            and all(value == str(F(value)) for value in values),
            'Unique sorted canonical exact rationals')
    result = {}
    for prefix, records in encoded['dual_buckets'].items():
        require(len(prefix) == 1 and prefix in '0123456789abcdef' and records,
                'Canonical nonempty dual hash bucket')
        for second, entries in records.items():
            require(len(second) == 1 and second in '0123456789abcdef' and entries,
                    'Canonical nonempty second dual hash bucket')
            for key, row in entries.items():
                require(len(key) == 64 and all(c in '0123456789abcdef' for c in key)
                        and key.startswith(prefix+second) and key not in result,
                        'Unique bucketed dual hash')
                require(isinstance(row, str), 'Textual exact dual indices')
                tokens = row.split(',')
                require(len(tokens) == 137 and all(token and token.isascii() and token.isdecimal()
                    and str(int(token)) == token and int(token) < len(values) for token in tokens),
                    'All 137 exact entries have canonical in-range indices')
                vector = [values[int(token)] for token in tokens]
                result[key] = {'nonzero_inequality_duals': {str(i): value
                    for i, value in enumerate(vector[:132]) if value != '0'},
                    'equality_duals': vector[132:136], 'raw_objective_upper': vector[136]}
    return result


def calculate(base, bank=None, proposer=None):
    io = module('joint_survival_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, quadratic, laws, identities_cert = map(read, ('all_selected_heavy_comparison',
        'expanded_seven_quadratic_comparison', 'expanded_seven_survival_comparison', 'load_two_cost_remainders'))
    pins = dict(PINS)
    for data in (prior, quadratic, laws, identities_cert):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent inherited source '+path)
            pins[path] = pin
    require(all(path in pins for path in ('certificates/source_norms/moments-survival/expanded_seven_quadratic_comparison.json',
        'certificates/source_norms/moments-survival/expanded_seven_survival_comparison.json',
        'certificates/source_norms/comparison-bounds/load_two_cost_remainders.json')), 'Every direct certificate is pinned')
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda name: module('joint_survival_'+name, io.named_artifact(base/'frontier', name+'.py'))
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

    problem = load('all_selected_heavy_comparison').AllSelectedHead(base, bank, proposer)
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
    require(oldU4 == 6*F(prior['standalone_hinge4_penalty']) == F(2005090285718827, 10584000000000000),
            'The complete211 separate AP13 comparison')
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
            'Every complete211 original function, independent test and positive weight retained')
    require(tags[48] == ('s', F(9)), 'Uniform raw-square9 is exactly original cost48')
    U9, T5 = old_costs[48], F(quadratic['second_factorial_tail_upper'])
    require(U9 == F(quadratic['uniform_raw_square9_upper']) == F(17859883, 4630500)
            and T5 == F(2303, 2700), 'Complete207 uniform raw-square and factorial bounds retained')
    direct, feedback, linear_records = list(old_costs), [], []
    linear_indices = load('expanded_seven_linear_comparison').INDICES
    require(linear_indices == (1, 2, 7, 10, 17, 18, 23, 26, 32, 33, 36),
            'The same eleven original affine-tail tests')
    for i in linear_indices:
        tag = tags[i]
        f = lambda n: original.source.zero5_cost(tag, n)
        degree, leading, constant, cutoff = original.source.zero5_cost_metadata(tag)
        co = {1: f(2)-f(1)} | {t: f(t+1)-2*f(t)+f(t-1) for t in range(2, 9)}
        expand = lambda n: f(1)+sum(c*max(n-t, 0) for t, c in co.items())
        require(degree == 1 and 1 <= cutoff <= 8 and min(co.values()) >= 0
                and sum(co.values()) > 0 and all(expand(n) == f(n) for n in range(1, 10))
                and sum(co.values()) == leading and f(1)-sum(t*c for t, c in co.items()) == constant,
                'Original linear cost at every positive integer load and along its full affine tail')
        scan = problem.scan(co)
        bound = f(1)*D+scan['complete_hinge_upper']
        direct[i] = min(old_costs[i], bound)
        linear_records.append({'index': i, 'tag': tag, 'at_one': f(1), 'tail_cutoff': cutoff,
            'complete_tail_slope': leading, 'complete_tail_constant': constant,
            'previous_cost_upper': old_costs[i], 'all_selected_upper': bound,
            'cost_upper': direct[i], 'weighted_gain': weights[i]*(old_costs[i]-direct[i]), 'scan': scan})
        print('Checked independent linear cost'+str(i)+': '+str(float(direct[i]))+', '
              +str(scan['counts']['joint'])+' exact dual uses.', flush=True)
    remainders = load('load_two_cost_remainders')
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
    retained_bank = {key: problem.bank[key] for key in sorted(problem.used)}
    return encode({'schema': 'erdos7-all-selected-survival-comparison-v2', 'source_sha256': pins,
        'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L, 'complete_square_upper': Q,
        'raw_lp': problem.lp.specification(), 'rational_duals': encode_dual_bank(retained_bank),
        'selected_policy': {1: [], **{t: [25,27,75,81] for t in range(2,9)}},
        'linear_indices': linear_indices, 'linear_results': linear_records,
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
        'joint_dual_uses': sum(r['scan']['counts']['joint'] for r in records+linear_records)+scan13['counts']['joint'],
        'scope': 'Four original AP11 block tests, the independent AP13 hinge and eleven original linear costs each use211 all-selected policy on the complete common raw-source LP, with all original residues and both seven depths. The uniform h4 result also feeds202 exact identities on each separate numerator test. Every original count tail,52 costs, signed mass and complete square remains on both whole saturated actual K faces. No shared optimizer across tests, positive load-two mass, actual attainment, off-face/global extension, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io = module('joint_survival_reader', args.base/'certificate_io.py')
    expected = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE))
    result = calculate(args.base, decode_dual_bank(expected['rational_duals']))
    require(result == expected, 'Exact complete common-source survival certificate')
    print('PASS: five complete survival tests, eleven linear tests, all52 costs and face='
          +str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
