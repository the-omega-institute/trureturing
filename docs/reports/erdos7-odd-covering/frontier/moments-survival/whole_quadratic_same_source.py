#!/usr/bin/env python3
"""Put factorial-head and lower-hinge terms in one actual-source LP.

All original test labels, surviving head corrections and complete
old/seven complements retain their meanings from109 and112.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
from math import gcd, lcm
from itertools import product

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/whole_quadratic_same_source.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/moments-survival/whole_quadratic_same_head.py': '84d7995521352aebd522659d189081eee31dbd200ccb4b1f638e7881d3c145b7',
    'certificates/source_norms/moments-survival/whole_quadratic_same_head.json': 'c0f131821927a5aaa8e6e4f1b9fa7ed972ee3c5481e78ff39234f2653a25704f',
}


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


class JointFactorialSource:
    """Nonnegative lower hinges and one factorial tail share a source LP."""
    def __init__(self, mean, factorial, mean_module, factorial_module):
        self.mean = mean
        self.factorial = factorial
        self.bridge = mean.bridge
        self.SCALE = mean_module.SCALE
        self.TOTAL = mean_module.TOTAL
        self.HEAD_SCALE = factorial_module.HEAD_SCALE
        self.PAIR_TAIL_UPPER = factorial_module.PAIR_TAIL_UPPER
        require(self.SCALE % 5 == 0 and self.TOTAL % self.HEAD_SCALE == 0,
                'All complete source and tail coefficients have exact integral scaling')
        require(mean.common.wi == factorial.wi and mean.common.caps ==
                [self.bridge.integer(360*x) for row in factorial.raw for x in row],
                'Mean and factorial terms retain exactly one common actual source')
        self.deep_raw = [[factorial.raw_rows[c][s]-6*factorial.raw[c][s]
                          for s in range(5)] for c in range(5)]

    def prepare(self, coefficients, theta):
        coefficients = {int(t): F(c) for t, c in coefficients.items() if F(c)}
        theta = F(theta)
        require(coefficients and theta > 0 and all(1 <= t <= 8 and c > 0 for t, c in coefficients.items()),
                'Nonnegative exact lower hinges and a positive factorial coefficient')
        values = list(coefficients.values())+[theta]
        denominator = lcm(*(v.denominator for v in values))
        nums = [self.bridge.integer(denominator*v) for v in values]
        divisor = gcd(*nums)
        factor = F(divisor, denominator)
        hinges = {t: self.bridge.integer(c/factor) for t, c in coefficients.items()}
        ti = self.bridge.integer(theta/factor)
        rec = self.mean.prepare(hinges)
        multiplier = self.bridge.integer(rec['factor'])
        return {'factor': factor, 'primitive_hinges': hinges, 'primitive_factorial': ti,
                'mean_record': rec, 'mean_multiplier': multiplier}

    def geometry(self, layout, B=None):
        if B is None:
            B = self.bridge.head_load(layout)
        r3, c9, s5, r15, s15, c45, s45 = layout
        compatible = r3 == self.bridge.ROOT[c9] == r15 and s5 == s15
        all_compatible = compatible and c45 == c9 and s45 == s5
        counts = [int(c == c45 and s == s45)+int(compatible and c == c9 and s == s5)
                  for c, s in product(range(5), repeat=2)]
        phi = [max(v-5, 0)*(v-4)//2 for v in B]
        source5 = [w*p+6*k for w, p, k in zip(self.factorial.wi, phi, counts)]
        parts = self.factorial.component_numerators(layout, B)
        old = F(parts[1], self.HEAD_SCALE)
        deep = (self.deep_raw[c45][s45]+(self.deep_raw[c9][s5] if compatible else F(0)))/5
        forced27 = F(0)
        if all_compatible and c9 == 1:
            forced27 = self.factorial.w[c9][s5]*self.factorial.raw[c9][s5]-self.factorial.head_caps[c9][s5]
        remainder = old+deep-forced27
        require(remainder >= 0, 'Complete remaining factorial-tail operator is nonnegative')
        raw_integral = sum(F(v, 5)*cap for v, cap in zip(source5, (x for row in self.factorial.raw for x in row)))
        require(raw_integral+remainder == self.factorial.factorial_head_bound(layout, B),
                'Exactly repartition the existing same-layout operator before the common LP')
        return {'source5': source5, 'remainder_scaled': self.bridge.integer(self.TOTAL*remainder),
                'old_tail': old, 'deep_positive7': deep, 'forced27': forced27,
                'mean_correction_scaled': self.bridge.integer(self.TOTAL*self.mean.correction(layout))}

    def objective(self, record, layout, B, extra, geometry=None):
        if geometry is None:
            geometry = self.geometry(layout, B)
        rec, mul, theta = record['mean_record'], record['mean_multiplier'], record['primitive_factorial']
        coefficients = [mul*rec['head'][weight, m][v]+theta*(self.SCALE//5)*lf
                        for weight, m, v, lf in zip(self.mean.common.wi, extra, B, geometry['source5'])]
        head, dual = self.bridge.lp_bound(coefficients, self.mean.common.caps, self.mean.common.budgets)
        selected = [mul*self.mean.common.tail([rec['increments'][i, weight, m][v]
                                              for weight, m, v in zip(self.mean.common.wi, extra, B)], a, b)
                    for i, (a, b) in enumerate(self.bridge.ORDER[:rec['highest_selected_label']], 1)]
        mean_charge = record['primitive_hinges'].get(1, 0)*geometry['mean_correction_scaled']
        value = mul*rec['constant']+45*head+sum(selected)+theta*geometry['remainder_scaled']-mean_charge
        require(value >= 0, 'Complete positive joint-source cost has a nonnegative bound')
        return value, {'scaled_joint_source_lp': head, 'source_dual': dual,
                       'scaled_selected_increments': selected, 'scaled_mean_deletion': mean_charge,
                       'scaled_factorial_remainder': theta*geometry['remainder_scaled']}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('joint_source_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = read('certificates/source_norms/moments-survival/whole_quadratic_same_head.json')
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited pin')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited input: '+path)
        used[path] = pin
    bridge = module('joint_source_bridge', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    cm = module('joint_source_common', base/'frontier/comparison-bounds/whole_cost_common_stop_loss.py')
    mm = module('joint_source_mean', base/'frontier/comparison-bounds/whole_cost_mean_stop_loss.py')
    fm = module('joint_source_factorial', base/'frontier/moments-survival/whole_factorial_same_head.py')
    qm = module('joint_source_quadratic', base/'frontier/moments-survival/whole_quadratic_same_head.py')
    mean = mm.MeanHead(bridge, read('certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json'), cm)
    joint = JointFactorialSource(mean, fm.FactorialHead(bridge), mm, fm)
    require(previous['faces'] == [{'vertices': [398, 410, 422], 'carrier': [1, 1]},
                                  {'vertices': [616, 628, 640], 'carrier': [1, 0]}]
            and previous['r'] == previous['rho'] == '0', 'Exactly the two complete actual saturated K faces')
    D, L, Q = map(F, (previous['mass'], previous['linear_upper'], previous['complete_square_upper']))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(374, 75))
            and F(previous['complete_tail_distinct_pairs']) == joint.PAIR_TAIL_UPPER,
            'Same actual mass and complete square and distinct-pair complements')
    # For every feasible source lambda, L>=0 and lambda<=raw imply
    # LP(F+theta*L)<=LP(F)+theta*sum(raw*L).  Check the exact
    # geometry identity needed to identify this right side with113.
    count, digest = 0, sha256()
    for layout in product(range(2), range(5), range(5), range(2), range(5), range(5), range(5)):
        B = bridge.head_load(layout)
        geometry = joint.geometry(layout, B)
        require(min(geometry['source5']) >= 0, 'Positive factorial source coefficient for cap domination')
        digest.update(json.dumps([layout, geometry['source5'], geometry['remainder_scaled']], separators=(',', ':')).encode())
        count += 1
    require(count == 12500, 'Every original head satisfies the source decomposition and domination premises')
    engine = module('joint_source_inventory', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    require(all(path in used and used[path] == pin for path, pin in engine.pins.items()), 'All original cost tags and source formulas pinned')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    results = []
    for prior in previous['quadratic_results']:
        index = prior['index']
        expansion = qm.quadratic_expansion(engine.source, tags[index])
        require(encode(expansion) == prior['expansion'], 'Same exact finite transitions and complete polynomial tail')
        if prior['status'] != 'enumerate':
            require(index == 46 and expansion['negative_hinge_coefficients'] == {t: F(-2) for t in range(5, 9)},
                    'The negative-hinge obstruction remains outside the positive operator')
            continue
        record = joint.prepare(expansion['hinge_coefficients'], expansion['factorial_tail_coefficient'])
        require(encode({k: record[k] for k in ('factor', 'primitive_hinges', 'primitive_factorial')}) == prior['scaling'],
                'Both operators use the identical primitive quadratic scaling')
        old_witness = prior['maximizing_witness']
        layout = tuple(old_witness['layout'])
        root, slot = old_witness['positive7_root'], old_witness['positive7_slot']
        B, extra = bridge.head_load(layout), mean.common.extra(root, slot)
        geometry = joint.geometry(layout, B)
        value, proof = joint.objective(record, layout, B, extra, geometry)
        bound = expansion['at_one']*D+record['factor']*F(value, mm.TOTAL)
        bound += expansion['factorial_tail_coefficient']*joint.PAIR_TAIL_UPPER
        require(bound == F(prior['uniform_cost_upper']),
                'A matching new-source primal/dual attains the old complete upper-bound maximum')
        rec = record['mean_record']
        old_value, old_proof = mean.objective(rec, layout, B, extra)
        same_head = record['mean_multiplier']*F(old_value, mm.TOTAL)
        same_head += record['primitive_factorial']*joint.factorial.factorial_head_bound(layout, B)
        require(same_head == F(value, mm.TOTAL), 'No source gain at this controlling old witness')
        allocation = [v for group in proof['source_dual'] for v in group['allocation']]
        require(len(allocation) == 25 and all(allocation[i] == mean.common.caps[i]
                    for i, coefficient in enumerate(geometry['source5']) if coefficient > 0),
                'The common source optimizer already fills every factorial-head support cap')
        require(proof['scaled_joint_source_lp'] == record['mean_multiplier']*old_proof['scaled_head_lp']
                +record['primitive_factorial']*(joint.SCALE//5)*sum(v*a for v, a in zip(geometry['source5'], allocation)),
                'The matched common allocation pays the lower-hinge and factorial source functions without loss')
        results.append({'index': index, 'tag': tags[index], 'scaling': prior['scaling'],
                        'joint_source_uniform_cost_upper': bound, 'previous_uniform_cost_upper': F(prior['uniform_cost_upper']),
                        'accepted_cost_upper': F(prior['accepted_cost_upper']), 'additional_gain': F(0),
                        'matching_witness': {'layout': layout, 'positive7_root': root, 'positive7_slot': slot,
                                             'geometry': geometry, **proof}})
    require([r['index'] for r in results] == [41, 42, 43, 44, 45, 47, 48, 49, 50, 51],
            'Every positive quadratic generator is closed by a matching source witness')
    costs, weights = list(map(F, previous['improved_cost_bounds'])), list(map(F, previous['cost_weights']))
    signed, square_weight = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    require(len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight,
            'All52 signed numerator terms and complete square complement retained')
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    require(N == F(previous['numerator_upper']), 'No additional numerator gain')
    tail = previous['full_count_tail']
    denominator = D-F(previous['standalone_hinge4_penalty'])-(sum(F(r['joint_mean_upper']) for r in previous['AP11_block_results'])
                   +F(tail['remaining_cost_upper']))/7
    require(denominator == F(previous['uniform_denominator_lower']) == F(50511415637, 632754738000),
            'Every full111 block and the independent AP13 loss remain')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    require(comparison == F(previous['comparison_upper']) > 403, 'No additional complete comparison gain is claimed')
    return {'schema': 'erdos7-whole-quadratic-same-source-v1', 'source_sha256': used,
            'faces': previous['faces'], 'mass': D, 'r': F(0), 'rho': F(0), 'linear_upper': L,
            'source_geometry_layout_count': count, 'all_source_geometries_sha256': digest.hexdigest(),
            'complete_tail_distinct_pairs': joint.PAIR_TAIL_UPPER, 'quadratic_results': results,
            'cost_weights': weights, 'improved_cost_bounds': costs, 'signed_mass_coefficient': signed,
            'complete_square_weight': square_weight, 'complete_square_upper': Q, 'numerator_upper': N,
            'additional_numerator_improvement': F(0), 'AP11_block_results': previous['AP11_block_results'],
            'full_count_tail': tail, 'standalone_hinge4_penalty': F(previous['standalone_hinge4_penalty']),
            'uniform_denominator_lower': denominator, 'offset': offset, 'comparison_upper': comparison,
            'additional_comparison_improvement': F(0),
            'scope': 'Ordinary stronger same-source bridge on both complete actual saturated K faces. For all ten positive quadratic generators the new operator is pointwise dominated by113 and an explicit matching LP primal/dual reaches its113 maximum; hence this refinement has no additional gain. All original residues,52 signed costs, polynomial and geometric tails and the full111 denominator remain. No actual covering-family attainment, off-face extension, Lean verification, global K or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('joint_source_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact same-source bridge and no-gain certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS:12500 source decompositions and10 matching exact LP witnesses; all ten113 maxima remain unchanged.')
    print('Complete comparison '+str(float(F(result['comparison_upper'])))+'; no additional numerator or comparison gain.')


if __name__ == '__main__':
    main()
