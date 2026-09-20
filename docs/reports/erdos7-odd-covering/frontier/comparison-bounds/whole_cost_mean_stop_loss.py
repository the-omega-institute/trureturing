#!/usr/bin/env python3
"""Combine the mean and every positive hinge on one original test layout.

The threshold-one head retains complete forced pure3 and deep-five
deletion information. All selected-label and peeled tails remain whole.
"""
import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from math import gcd, lcm
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/whole_cost_mean_stop_loss.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/comparison-bounds/whole_cost_common_stop_loss.py': 'c220594349efc9a422b25e9bd434bb4508d4665b7ae80459e5cd14277d6df850',
    'certificates/source_norms/comparison-bounds/whole_cost_common_stop_loss.json': '25fa8fd2564e2da46575f04405d6e4d8eba56bc8e6df67a563a14ec887b6753e',
    'frontier/endpoint-bounds/endpoint_k_face_forced27.py': '8ea52815e6ae5b9b4df5733a8c8bae8f0704a12da0d531d794873406f0f29c87',
    'certificates/source_norms/endpoint-bounds/endpoint_k_face_forced27.json': '59202ce65324295b32b028f6b67f90e4a7b8bbba5f62608a43f9bc4979dc8e79',
    'frontier/moments-survival/whole_face_second_factorial_tail.py': '106e081ed80b09a176ca63aa382c5486d3a980c34c04617115f764131b84a0cf',
    'certificates/source_norms/moments-survival/whole_face_second_factorial_tail.json': '2cf56c20350e698147a3ed004f23bde00990766fe876c18b61e4444f16e99465',
}
SCALE = 5*7**7
TOTAL = SCALE*16200
Q_SLOTS = (F(0), F(1, 5), F(1, 5), F(3, 20), F(1, 5))
MEAN_SUPPORTS = (((0, 1, 2, 1, 2, 3, 2), 1, 4),
                 ((1, 1, 2, 1, 2, 3, 2), 1, 4))


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


class MeanHead:
    """A positive hinge combination, with its same-layout mean correction.

    prepare(coefficients) accepts rational coefficients indexed by t=1..8.
    objective(record, layout, B, extra) returns the scaled primitive value.
    The actual bound is record['factor']*value/TOTAL. A constant multiple
    of the exact survivor mass is added by the caller, after this maximum.
    """
    def __init__(self, bridge, stop_loss, common_module):
        self.bridge = bridge
        augmented = deepcopy(stop_loss)
        profile = augmented['stop_loss_profile']
        profile['selected_prefix_lengths']['1'] = 0
        profile['surviving_old_remainders']['1'] = profile['complete_surviving_old_tail']
        self.common = common_module.CommonHead(bridge, augmented)
        self.profile = self.common.profile
        require(common_module.SCALE == SCALE and common_module.TOTAL == TOTAL, 'Identical exact bridge scaling')
        for weight, extra in product(sorted(set(self.common.wi)), range(3)):
            self.common.raw_costs[1, weight, extra] = [0]+[bridge.integer(SCALE*(F(weight, 5)*(v-1)
                      +bridge.seven_increment(1, v, extra))) for v in range(1, 12)]
        require(bridge.ROOT == (0, 0, 1, 1, 1) and bridge.ETA == (F(1, 18),)+(F(1, 9),)*4,
                'Canonical actual whole-face source and retained shallow families')

    def correction_parts(self, layout):
        r3, c9, s5, r15, s15, c45, s45 = layout
        eta = self.bridge.ETA
        pure3 = (F(int(r3 == 0), 120)+F(int(c9 == 1), 180)+Q_SLOTS[s5]/90
                 +(Q_SLOTS[s15]/90 if r15 == 0 else F(0))
                 +(Q_SLOTS[s45]/135 if c45 == 1 else F(0)))
        deep5 = ((1+r3)*sum(eta[j] for j in range(5) if self.bridge.ROOT[j] == r3)
                 +(1+self.bridge.ROOT[c9])*eta[c9])/100
        return pure3, deep5

    def correction(self, layout):
        return sum(self.correction_parts(layout))

    def prepare(self, coefficients):
        coefficients = {int(t): F(v) for t, v in coefficients.items() if F(v)}
        require(coefficients and all(1 <= t <= 8 and v > 0 for t, v in coefficients.items()),
                'A nonzero nonnegative combination of the original thresholds')
        denominator = lcm(*(v.denominator for v in coefficients.values()))
        numerators = {t: int(v*denominator) for t, v in coefficients.items()}
        divisor = gcd(*numerators.values())
        integers = {t: v//divisor for t, v in numerators.items()}
        factor = F(divisor, denominator)
        require(all(factor*integers[t] == v for t, v in coefficients.items()), 'Exact primitive positive hinge scaling')
        highest = max(self.common.prefix[t] for t in integers)
        head = {(weight, extra): [0]+[sum(c*self.common.raw_costs[t, weight, extra][v] for t, c in integers.items())
                                      for v in range(1, 7)]
                for weight, extra in product(sorted(set(self.common.wi)), range(3))}
        increments = {(i, weight, extra): [0]+[sum(c*(self.common.raw_costs[t, weight, extra][v+i]
                                      -self.common.raw_costs[t, weight, extra][v+i-1])
                                      for t, c in integers.items() if self.common.prefix[t] >= i)
                                      for v in range(1, 7)]
                      for i, weight, extra in product(range(1, highest+1), sorted(set(self.common.wi)), range(3))}
        constant = self.bridge.integer(TOTAL*sum(c*(F(self.profile['complete_complementary_positive7_tail'])
                    +F(self.profile['surviving_old_remainders'][str(t)])) for t, c in integers.items()))
        return {'coefficients': coefficients, 'factor': factor, 'primitive_coefficients': integers,
                'highest_selected_label': highest, 'constant': constant, 'head': head, 'increments': increments}

    def objective(self, record, layout, B, extra):
        value, detail = self.common.objective(record, B, extra)
        correction = record['primitive_coefficients'].get(1, 0)*self.bridge.integer(TOTAL*self.correction(layout))
        require(value >= correction >= 0, 'Complete positive objective remains above its certified head deletion')
        return value-correction, {**detail, 'scaled_mean_head_correction': correction}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('mean_stop_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = read('certificates/source_norms/moments-survival/whole_face_second_factorial_tail.json')
    common = read('certificates/source_norms/comparison-bounds/whole_cost_common_stop_loss.json')
    forced = read('certificates/source_norms/endpoint-bounds/endpoint_k_face_forced27.json')
    for prior in (previous, common, forced):
        for path, pin in prior['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited input: '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited input: '+path)
            used[path] = pin
    stop_loss = read('certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json')
    old_module = module('mean_stop_old', base/'frontier/comparison-bounds/whole_cost_common_stop_loss.py')
    bridge = module('mean_stop_bridge', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    parent = module('mean_stop_profile', base/'frontier/comparison-bounds/whole_face_stop_loss_generator.py')
    problem = MeanHead(bridge, stop_loss, old_module)
    D, L = F(previous['mass']), F(previous['linear_upper'])
    require(D == F(53, 360) and L == F(1151, 1800) and previous['r'] == previous['rho'] == '0',
            'Exactly the same saturated whole faces and retained first moment')
    old_costs, weights = list(map(F, previous['improved_cost_bounds'])), list(map(F, previous['cost_weights']))
    require(old_costs[:41] == list(map(F, common['improved_cost_bounds'][:41]))
            and len(old_costs) == len(weights) == 52, 'Retain104 linear bounds and108 complete quadratic bounds')
    require(F(3, 4)*F(1, 18)/5 == F(1, 120)
            and F(1, 18)/5 == F(1, 90) and F(1, 27)/5 == F(1, 135)
            and F(3, 4)*F(1, 135) == F(1, 180), 'Complete pure3 and forced27 deletion coefficients')
    require(F(forced['complete_deep3_deletion']) == F(1, 120)
            and F(forced['deep3_five_complement_coefficient']) == F(1, 90)
            and F(forced['forced27_cell1_deletion']) == F(1, 180)
            and all(tuple(map(F, row['pure5_complement_in_slots'])) == Q_SLOTS
                    for row in forced['first_beta_slot_tables']), 'The correction uses exactly75 whole-face deletion data')
    require(F(1, 25)/(1-F(1, 5))/5 == F(1, 100), 'Entire forbidden deep-five geometric deletion coefficient')
    require(sum(Q_SLOTS) == F(3, 4), 'Exact complete pure5 complement in the five source slots')
    engine = module('mean_stop_engine', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    require(all(path in used and used[path] == pin for path, pin in engine.pins.items()), 'Pinned complete cost inventory')
    U = {int(t): F(value) for t, value in stop_loss['stop_loss_profile']['uniform_hinge_uppers'].items()}
    fixed_layouts = list(old_module.FIXED_LAYOUTS)+list(MEAN_SUPPORTS)
    for row in common['cost_results']:
        if 'maximizing_witness' in row:
            witness = row['maximizing_witness']
            choice = (tuple(witness['layout']), witness['positive7_root'], witness['positive7_slot'])
            if choice not in fixed_layouts:
                fixed_layouts.append(choice)
    records = []
    for i, row in enumerate(stop_loss['linear_cost_updates']):
        require(row['index'] == i and row['name'] == engine.specs[i]['name']
                and row['tuple'] == engine.specs[i]['tuple'], 'Every original independent test identity')
        expansion = parent.linear_cost_profile(engine.source, engine.specs[i]['tag'], D, U)
        require(encode(expansion) == row['expansion'], 'Exact original cost through its complete affine tail')
        coefficients = dict(expansion['curvatures']) | {1: expansion['first_difference']}
        objective = problem.prepare(coefficients)
        constant = expansion['at_one']*D
        supports = []
        for layout, root, slot in fixed_layouts:
            value, detail = problem.objective(objective, layout, bridge.head_load(layout), problem.common.extra(root, slot))
            supports.append({'layout': layout, 'positive7_root': root, 'positive7_slot': slot,
                             'value': constant+objective['factor']*F(value, TOTAL),
                             'mean_head_correction_parts': problem.correction_parts(layout), **detail})
        if sum(v > 0 for v in expansion['curvatures'].values()) == 1:
            support = next(s for s in supports if (tuple(s['layout']), s['positive7_root'], s['positive7_slot']) == MEAN_SUPPORTS[0])
            require(support['value'] >= old_costs[i], 'One exact common support excludes every single-curvature cost')
        support = max(supports, key=lambda x: x['value'])
        records.append({'index': i, 'name': row['name'], 'tuple': row['tuple'],
                        'constant_mass_term': constant, 'objective': objective,
                        'previous_cost_bound': old_costs[i], 'fixed_layout_lower_support': support,
                        'status': 'fixed-layout-obstruction' if support['value'] >= old_costs[i] else 'enumerate'})
    require(len(records) == 41, 'All original linear-growth costs, including the first moment')
    require(records[40]['fixed_layout_lower_support']['value'] == F(897, 1400) > L,
            'The affine generator is excluded by an explicit original layout')
    require([r['index'] for r in records if r['status'] == 'enumerate']
            == [1, 2, 7, 10, 17, 18, 23, 26, 32, 33, 36],
            'Fixed valid supports exclude all other proposed mean/hinge objectives')
    groups, by_key = [], {}
    for row in records:
        if row['status'] != 'enumerate':
            continue
        key = tuple(sorted(row['objective']['primitive_coefficients'].items()))
        if key not in by_key:
            by_key[key] = len(groups)
            groups.append({'id': len(groups), 'objective': row['objective'], 'cost_indices': []})
        group = by_key[key]
        row['objective_group'] = group
        groups[group]['cost_indices'].append(row['index'])
    print('New mean/hinge objectives: '+str(len(groups))+' primitive groups for '
          +str(sum(len(g['cost_indices']) for g in groups))+' costs; fixed obstructions '
          +str([r['index'] for r in records if r['status'] != 'enumerate']), flush=True)
    best, witnesses, ties = {}, {}, {g['id']: 0 for g in groups}
    digest, count = sha256(), 0
    extras = [(root, slot, problem.common.extra(root, slot)) for root, slot in product(range(2), range(5))]
    for li, layout in enumerate(product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))):
        B = bridge.head_load(layout)
        # The correction is a fixed complete source quantity for this head.
        correction = bridge.integer(TOTAL*problem.correction(layout))
        for root, slot, extra in extras:
            for group in groups:
                gid, objective = group['id'], group['objective']
                value, detail = problem.common.objective(objective, B, extra)
                charge = objective['primitive_coefficients'].get(1, 0)*correction
                require(value >= charge >= 0, 'Every new common objective retains its certified positive head')
                value -= charge
                digest.update(json.dumps([li, root, slot, gid, value], separators=(',', ':')).encode())
                count += 1
                if gid not in best or value > best[gid]:
                    best[gid], ties[gid] = value, 1
                    witnesses[gid] = {'layout': layout, 'positive7_root': root, 'positive7_slot': slot,
                                      'scaled_mean_head_correction': charge,
                                      'mean_head_correction_parts': problem.correction_parts(layout), **detail}
                elif value == best[gid]:
                    ties[gid] += 1
        if (li+1) % 2500 == 0:
            print('New common mean/hinge heads '+str(li+1)+'/12500', flush=True)
    require(count == len(groups)*125000, 'Every original head and independent21/35 projection in each new primitive objective')
    direct, results = list(old_costs), []
    for row in records:
        i, objective = row['index'], row['objective']
        result = {k: v for k, v in row.items() if k != 'objective'}
        result['objective'] = {k: v for k, v in objective.items() if k not in ('head', 'increments')}
        if row['status'] == 'enumerate':
            gid = row['objective_group']
            bound = row['constant_mass_term']+objective['factor']*F(best[gid], TOTAL)
            require(bound >= row['fixed_layout_lower_support']['value'], 'The complete maximum dominates its fixed support')
            direct[i] = min(old_costs[i], bound)
            result.update({'uniform_cost_upper': bound, 'maximizing_witness': witnesses[gid], 'maximizer_count': ties[gid]})
        result['accepted_cost_upper'] = direct[i]
        result['weighted_direct_gain'] = weights[i]*(old_costs[i]-direct[i])
        results.append(result)
    require(direct[41:] == old_costs[41:], 'Every108 quadratic and complete raw81 bound is retained')
    source, specs = engine.source, engine.specs+engine.quadratic_specs
    consumer = module('mean_stop_consumer', base/'frontier/endpoint-bounds/vector_face_complete_ratio.py')
    majorant = module('mean_stop_majorant', base/'frontier/endpoint-bounds/endpoint_numerator_common_costs.py')
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    functions = [lambda n, tag=tag: source.zero5_cost(tag, n) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    Q = F(previous['complete_square_upper'])
    costs, proofs = consumer.propagate(majorant, functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    require(len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight
            and Q == F(374, 75), 'All signed costs and both complete square-complement tails')
    old_N = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    direct_gain = sum(w*(a-b) for w, a, b in zip(weights, old_costs, direct))
    propagation = sum(w*(a-b) for w, a, b in zip(weights, direct, costs))
    require(old_N == F(previous['numerator_upper']) and old_N-N == direct_gain+propagation
            and direct_gain > 0 and propagation >= 0 and N > 0, 'All complete numerator improvements balance once')
    denominator = F(previous['uniform_denominator_lower'])
    coeff = {k: F(v) for k, v in previous['denominator_coefficients'].items()}
    require(denominator == coeff['mass']*D-coeff['linear']*L-sum(coeff['hinge'+str(t)]*U[t] for t in range(2, 6))
            == F(1358432973299, 17084377926000), 'Retain the whole101 AP11 denominator with its old uniform first moment')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    require(offset+old_N/denominator == F(previous['comparison_upper'])
            and 403 < comparison < F(previous['comparison_upper']), 'Same complete comparison, improved on the faces and still above403')
    return {'schema': 'erdos7-whole-cost-mean-stop-loss-v1', 'source_sha256': used,
            'faces': previous['faces'], 'mass': D, 'r': F(0), 'rho': F(0), 'linear_upper': L,
            'pure5_complement_slots': Q_SLOTS, 'mean_selected_prefix_length': 0,
            'mean_old_tail': F(problem.profile['complete_surviving_old_tail']),
            'mean_positive_tail': F(problem.profile['complete_complementary_positive7_tail']),
            'cost_results': results, 'primitive_objective_groups': [{'id': g['id'], 'cost_indices': g['cost_indices']} for g in groups],
            'joint_layout_checks': count, 'all_joint_objectives_sha256': digest.hexdigest(),
            'integer_bridge_scale': SCALE, 'integer_objective_scale': TOTAL,
            'cost_weights': weights, 'direct_cost_upper_bounds': direct, 'majorants': proofs, 'improved_cost_bounds': costs,
            'improved_linear_upper': direct[40], 'signed_mass_coefficient': signed,
            'complete_square_weight': square_weight, 'complete_square_upper': Q,
            'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
            'direct_numerator_improvement_over108': direct_gain, 'majorant_propagation_improvement': propagation,
            'total_numerator_improvement_over108': old_N-N, 'previous_numerator': old_N, 'numerator_upper': N,
            'uniform_hinge_uppers': U, 'denominator_coefficients': coeff, 'full_AP11_tail': previous['full_AP11_tail'],
            'uniform_denominator_lower': denominator, 'offset': offset, 'previous_comparison': F(previous['comparison_upper']),
            'comparison_upper': comparison, 'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'scope': 'Ordinary uniform result on both complete actual K-control beta faces with r=rho=0 and mass53/360. One original test supplies its mean, every hinge, head and selected cylinders. Complete extra pure3 and deep-five deletions strengthen only the mean head; all weighted peeled tails remain. Retains108 complete quadratic costs, all52 signed terms and the complete101 denominator. No off-face extension, new global K, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('mean_stop_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact canonical whole-cost mean/hinge certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: common mean/hinge layouts, full extra deletion, all52 costs and complete101 denominator.')
    print('Comparison '+str(float(F(result['comparison_upper'])))+'; direct numerator gain '+str(float(F(result['direct_numerator_improvement_over108'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
