#!/usr/bin/env python3
"""Keep one original test layout across all hinges of each complete AP cost.

Each retained original cylinder receives its combined nonnegative objective
before its maximum. Different AP costs retain independent original tests.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import gcd, lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/whole_cost_common_stop_loss.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/comparison-bounds/whole_face_stop_loss_generator.py': '47fb9812f29652ad3bb24919bbf466e26c02e6e3976ca0b40d19f508b8dc3aa9',
    'certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json': 'f9cbfcee82a6011e83dfb5571fb89f28a6eacbfee89c98fb8216c1e41a52a644',
    'frontier/moments-survival/whole_face_ap11_survival.py': '73547fa6455e9e3c613f3c7166537c1f048177998c611ade97996720a549cf76',
    'certificates/source_norms/moments-survival/whole_face_ap11_survival.json': '17259c5e49d417f5fa58dc794ac3a2447e3f5c7396447ef5dccf89ce4b0f1a16',
}
SCALE = 5*7**7
TOTAL = SCALE*16200
FIXED_LAYOUTS = (((0, 1, 2, 1, 2, 1, 1), 1, 4),
                 ((0, 1, 2, 0, 2, 1, 1), 0, 2),
                 ((0, 1, 2, 0, 2, 1, 2), 0, 2))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


class CommonHead:
    def __init__(self, bridge, stop_loss):
        self.bridge = bridge
        self.profile = stop_loss['stop_loss_profile']
        pre, raw, w, descendant = bridge.source_tables(2)
        require(encode(raw) == self.profile['source_upper_table'] and encode(w) == self.profile['retained_density']
                and encode(descendant) == self.profile['descendant5_coefficients'], 'Exactly the whole-face source of98')
        self.p = [[bridge.integer(20*x) for x in row] for row in pre]
        self.q = [[bridge.integer(18*x) for x in row] for row in descendant]
        self.wi = [bridge.integer(5*x) for row in w for x in row]
        self.caps = [bridge.integer(360*x) for row in raw for x in row]
        self.budgets = [bridge.integer(360*x) for x in bridge.GROUP_MASSES]
        self.prefix = {int(t): k for t, k in self.profile['selected_prefix_lengths'].items()}
        self.raw_costs = {(t, weight, extra): [0]+[bridge.integer(SCALE*(F(weight, 5)*max(v-t, 0)
                                  +bridge.seven_increment(t, v, extra))) for v in range(1, 12)]
                          for t, weight, extra in product(range(2, 9), sorted(set(self.wi)), range(3))}

    def tail(self, coefficients, a, b):
        require(min(coefficients) >= 0, 'Combined selected-label coefficient is nonnegative')
        if b == 0:
            require(a in (3, 4), 'Selected pure3 original label')
            value = max(sum(self.p[c][s]*coefficients[5*c+s] for s in range(5)) for c in range(5))
            return (16200//(20*3**a))*value
        require(b == 2 and a in (0, 1), 'Selected descendant-five original label')
        if a == 0:
            value = max(sum(self.q[c][s]*coefficients[5*c+s] for c in range(5)) for s in range(5))
        else:
            value = max(sum(self.q[c][s]*coefficients[5*c+s] for c in range(5) if self.bridge.ROOT[c] == r)
                        for r, s in product(range(2), range(5)))
        return 36*value

    def extra(self, root, slot):
        return [int(self.bridge.ROOT[c] == root)+int(s == slot) for c, s in product(range(5), repeat=2)]

    def prepare(self, row, D, U1, old_bound):
        curvature = {int(t): F(value) for t, value in row['expansion']['curvatures'].items() if F(value)}
        common = {'index': row['index'], 'curvature': curvature, 'old_bound': old_bound,
                  'affine_bound': F(row['expansion']['at_one'])*D+F(row['expansion']['first_difference'])*U1}
        if len(curvature) <= 1:
            common['status'] = 'homogeneous-single-hinge' if curvature else 'affine'
            require(old_bound <= F(row['expansion']['cost_upper']), 'No improvement from recomputing the same homogeneous bound')
            return common
        denominator = lcm(*(value.denominator for value in curvature.values()))
        numerators = {t: int(value*denominator) for t, value in curvature.items()}
        divisor = gcd(*numerators.values())
        integers, factor = {t: value//divisor for t, value in numerators.items()}, F(divisor, denominator)
        require(all(factor*integers[t] == value for t, value in curvature.items())
                and gcd(*integers.values()) == 1, 'Exact primitive integer curvature vector')
        highest = max(self.prefix[t] for t in integers)
        head = {(weight, extra): [0]+[sum(c*self.raw_costs[t, weight, extra][v] for t, c in integers.items())
                                     for v in range(1, 7)] for weight, extra in product(sorted(set(self.wi)), range(3))}
        increments = {(i, weight, extra): [0]+[sum(c*(self.raw_costs[t, weight, extra][v+i]
                                  -self.raw_costs[t, weight, extra][v+i-1]) for t, c in integers.items() if self.prefix[t] >= i)
                                  for v in range(1, 7)]
                      for i, weight, extra in product(range(1, highest+1), sorted(set(self.wi)), range(3))}
        constant = self.bridge.integer(TOTAL*sum(c*(F(self.profile['complete_complementary_positive7_tail'])
                                  +F(self.profile['surviving_old_remainders'][str(t)])) for t, c in integers.items()))
        common.update({'factor': factor, 'primitive_curvature': integers, 'head': head, 'increments': increments,
                       'highest_selected_label': highest, 'constant': constant})
        lower_supports = []
        for layout, root, slot in FIXED_LAYOUTS:
            value, detail = self.objective(common, self.bridge.head_load(layout), self.extra(root, slot))
            lower_supports.append({'layout': layout, 'positive7_root': root, 'positive7_slot': slot,
                                   'value': common['affine_bound']+factor*F(value, TOTAL), **detail})
        common['fixed_layout_lower_support'] = max(lower_supports, key=lambda x: x['value'])
        common['status'] = 'fixed-layout-obstruction' if common['fixed_layout_lower_support']['value'] >= old_bound else 'enumerate'
        return common

    def objective(self, record, B, extra):
        coefficients = [record['head'][weight, m][v] for weight, m, v in zip(self.wi, extra, B)]
        head, dual = self.bridge.lp_bound(coefficients, self.caps, self.budgets)
        selected = [self.tail([record['increments'][i, weight, m][v] for weight, m, v in zip(self.wi, extra, B)], a, b)
                    for i, (a, b) in enumerate(self.bridge.ORDER[:record['highest_selected_label']], 1)]
        return record['constant']+45*head+sum(selected), {'scaled_head_lp': head, 'scaled_selected_increments': selected, 'head_dual': dual}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('common_cost_stop_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = read('certificates/source_norms/moments-survival/whole_face_ap11_survival.json')
    stop_loss = read('certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json')
    for data in (previous, stop_loss):
        for path, pin in data['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin: '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited input: '+path)
            used[path] = pin
    D, L = F(previous['mass']), F(previous['linear_upper'])
    U = {int(t): F(value) for t, value in stop_loss['stop_loss_profile']['uniform_hinge_uppers'].items()}
    retained = previous['retained_numerator']
    old_costs, weights = list(map(F, retained['cost_upper_bounds'])), list(map(F, retained['cost_weights']))
    require(D == F(53, 360) and U[1] == L-D and previous['r'] == previous['rho'] == '0'
            and encode(old_costs) == stop_loss['improved_cost_bounds'], 'Same101 saturated faces and complete98 cost bounds')
    engine = module('common_cost_stop_engine', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    parent = module('common_cost_stop_parent', base/'frontier/comparison-bounds/whole_face_stop_loss_generator.py')
    bridge = module('common_cost_stop_bridge', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    problem = CommonHead(bridge, stop_loss)
    records = []
    for i, row in enumerate(stop_loss['linear_cost_updates']):
        require(row['index'] == i and row['name'] == engine.specs[i]['name'] and row['tuple'] == engine.specs[i]['tuple'], 'Original cost identity')
        expansion = parent.linear_cost_profile(engine.source, engine.specs[i]['tag'], D, U)
        require(encode(expansion) == row['expansion'], 'Exact all-load curvature and complete affine tail')
        records.append(problem.prepare(row, D, U[1], old_costs[i]))
    active = [record for record in records if record['status'] == 'enumerate']
    require([record['index'] for record in active] == [1, 2, 7, 10, 17, 18, 23, 26, 32, 33, 36], 'Eleven genuinely unresolved joint objectives')
    require([record['index'] for record in records if record['status'] == 'fixed-layout-obstruction'] == [0, 16]
            and sum(record['status'] == 'homogeneous-single-hinge' for record in records) == 27
            and records[40]['status'] == 'affine', 'Exact no-improvement dispositions for every other cost')
    best, witnesses, ties = {}, {}, {record['index']: 0 for record in active}
    digest, count = sha256(), 0
    extras = [(root, slot, problem.extra(root, slot)) for root, slot in product(range(2), range(5))]
    for li, layout in enumerate(product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))):
        B = bridge.head_load(layout)
        for root, slot, extra in extras:
            for record in active:
                i = record['index']
                value, detail = problem.objective(record, B, extra)
                digest.update(json.dumps([li, root, slot, i, value], separators=(',', ':')).encode())
                count += 1
                if i not in best or value > best[i]:
                    best[i], ties[i] = value, 1
                    witnesses[i] = {'layout': layout, 'positive7_root': root, 'positive7_slot': slot, **detail}
                elif value == best[i]:
                    ties[i] += 1
    require(count == 1375000, 'Every original head and positive7 projection for all eleven remaining costs')
    direct, results = list(old_costs), []
    for record in records:
        i = record['index']
        result = {key: value for key, value in record.items() if key not in ('head', 'increments')}
        if record['status'] == 'enumerate':
            bound = record['affine_bound']+record['factor']*F(best[i], TOTAL)
            require(bound >= record['fixed_layout_lower_support']['value'], 'The exhaustive maximum dominates its fixed lower support')
            require(bound < old_costs[i], 'Every enumerated joint-cost bound improves the current complete cost')
            direct[i] = bound
            result.update({'uniform_cost_upper': bound, 'maximizing_witness': witnesses[i], 'maximizer_count': ties[i]})
        result['accepted_cost_upper'] = direct[i]
        results.append(result)
    source, specs = engine.source, engine.specs+engine.quadratic_specs
    Q = F(retained['complete_square_upper'])
    consumer = module('common_cost_stop_consumer', base/'frontier/endpoint-bounds/vector_face_complete_ratio.py')
    majorant = module('common_cost_stop_majorant', base/'frontier/endpoint-bounds/endpoint_numerator_common_costs.py')
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    functions = [lambda n, tag=tag: source.zero5_cost(tag, n) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    costs, proofs = consumer.propagate(majorant, functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = F(retained['signed_mass_coefficient']), F(retained['complete_square_weight'])
    require(len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight and Q == F(374, 75), 'All signed and complete square terms')
    old_N = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    direct_gain = sum(w*(a-b) for w, a, b in zip(weights, old_costs, direct))
    propagated = sum(w*(a-b) for w, a, b in zip(weights, direct, costs))
    require(old_N == F(retained['numerator_upper']) and old_N-N == direct_gain+propagated
            and direct_gain > 0 and propagated >= 0 and N > 0, 'The complete numerator improvement balances without duplicate payments')
    coeff = {key: F(value) for key, value in previous['denominator_coefficients'].items()}
    denominator = coeff['mass']*D-coeff['linear']*L-sum(coeff['hinge'+str(t)]*U[t] for t in range(2, 6))
    require(denominator == F(previous['uniform_denominator_lower']) == F(1358432973299, 17084377926000) > 0, 'Unchanged complete101 AP11 denominator')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    require(offset+old_N/denominator == F(previous['comparison_upper']) and 403 < comparison < F(previous['comparison_upper']), 'Strict face improvement with the same positive denominator, still above403')
    return {'schema': 'erdos7-whole-cost-common-stop-loss-v1', 'source_sha256': used,
            'faces': previous['faces'], 'mass': D, 'r': F(0), 'rho': F(0), 'linear_upper': L,
            'cost_results': results, 'joint_layout_checks': count, 'all_joint_objectives_sha256': digest.hexdigest(),
            'integer_bridge_scale': SCALE, 'integer_objective_scale': TOTAL,
            'cost_weights': weights, 'direct_cost_upper_bounds': direct, 'majorants': proofs, 'improved_cost_bounds': costs,
            'signed_mass_coefficient': signed, 'complete_square_weight': square_weight, 'complete_square_upper': Q,
            'direct_numerator_improvement': direct_gain, 'majorant_propagation_improvement': propagated,
            'total_numerator_improvement': old_N-N, 'previous_numerator': old_N, 'numerator_upper': N,
            'uniform_hinge_uppers': U, 'denominator_coefficients': coeff, 'full_AP11_tail': previous['full_AP11_tail'],
            'uniform_denominator_lower': denominator, 'offset': offset, 'previous_comparison': F(previous['comparison_upper']),
            'comparison_upper': comparison, 'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'scope': 'Ordinary uniform result on both complete actual K-control faces with r=rho=0 and mass53/360. All hinges of one AP cost retain one original test layout; different costs remain independent. Every selected original label uses one combined nonnegative objective, with complete weighted peeled remainders. Preserves all52 costs and the complete101 denominator. No off-face extension, new global K, Lean verification or unrestricted Erdos7 claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('common_cost_stop_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical common-layout whole-cost certificate')
    elif args.write or args.output is not None:
        io.write_certificate_text(args.output or args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: exact same-test hinge coupling,1375000 complete joint layout/LP checks, all52 costs and full101 denominator.')
    print('Comparison '+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
