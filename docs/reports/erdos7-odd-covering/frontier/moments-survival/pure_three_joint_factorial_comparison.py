#!/usr/bin/env python3
"""Couple the complete pure-three head cross and pair tail, retaining the pure-five gain."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
from math import lcm
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/moments-survival/pure_three_joint_factorial_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/moments-survival/pure_three_joint_moments.py': 'dcd5dae8b9ff0ef9c79f7ad7a52183079226815d2bf229f3ebcae349b9d70351', 'certificates/source_norms/moments-survival/pure_three_joint_moments.json': 'ed70ad34510621ef839a4dc770c5fe0c7000f6995141d64f2e3e300bc4aa9e4b', 'frontier/moments-survival/pure_five_joint_factorial_comparison.py': '5a1448675aea32e0a7d6103e1b29af3c965896bdd4d62027b40f357b77846042', 'certificates/source_norms/moments-survival/pure_five_joint_factorial_comparison.json': '683b75b5706681b5081d4384401615882119cea7d069632bca3647cf1c1bdbac'}


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


class JointThreeHead:
    """Replace precisely the deep-three head-cross/pair block on the same layout."""
    def __init__(self, old, density, five):
        self.old, self.density, self.five = old, density, five
        require(tuple(density) == (F(7, 10), F(11, 20), F(3, 10), F(3, 10), F(3, 10)),
                'The five independently proved actual deep-three cell caps')

    def components(self, layout, B=None):
        if B is None:
            B = self.five.bridge.head_load(layout)
        prior = self.five.components(layout, B)
        table = self.old
        h4 = [max(b-4, 0) for b in B]
        rows = [sum(table.pre[c][s]*table.w[c][s]*h4[5*c+s] for s in range(5))
                for c in range(5)]
        candidates = [a/18+c/36 for a, c in zip(rows, self.density)]
        old_cross = max(rows)/18
        difference = max(candidates)-old_cross-F(7, 360)
        require(difference <= 0, 'Every density is at most7/10, so each complete block improves weakly')
        return {'old_head': prior['head_upper'], 'pure_five_components': prior,
                'pure_three_pre_max_rows': rows, 'joint_three_candidates': candidates,
                'joint_three_upper': max(candidates), 'old_pure_three_cross': old_cross,
                'replacement_difference': difference, 'adopted_difference': difference,
                'head_upper': prior['head_upper']+difference}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('five_factorial_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    previous = read('certificates/source_norms/moments-survival/pure_three_joint_moments.json')
    prior_factorial = read('certificates/source_norms/moments-survival/pure_five_joint_factorial_comparison.json')
    quadratic = read('certificates/source_norms/moments-survival/whole_quadratic_same_head.json')
    joint = read('certificates/source_norms/moments-survival/pure_five_joint_moments.json')
    old_factorial = read('certificates/source_norms/moments-survival/whole_factorial_same_head.json')
    old_partition = read('certificates/source_norms/moments-survival/complete_off_face_factorial_tail.json')
    used = dict(PINS)
    for data in (previous, quadratic, joint, old_factorial, old_partition):
        for path, pin in data['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin: '+path)
            used[path] = pin
    for path, pin in used.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    load = lambda name: module('five_factorial_'+name, io.named_artifact(base/'frontier', name+'.py'))
    bridge, common = load('k_face_common_seven_hinges'), load('whole_cost_common_stop_loss')
    mean_module, factorial_module = load('whole_cost_mean_stop_loss'), load('whole_factorial_same_head')
    quad, complete = load('whole_quadratic_same_head'), load('complete_off_face_factorial_tail')
    mean = mean_module.MeanHead(bridge, read('certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json'), common)
    factorial = factorial_module.FactorialHead(bridge)
    five = load('pure_five_joint_factorial_comparison').JointFiveHead(bridge, factorial, tuple(map(F, joint['deep_density_caps'])))
    problem = JointThreeHead(factorial, tuple(map(F, previous['deep_density_caps'])), five)
    require(joint['slot_order'] == ['P', 'A', 'B', 'Q', 'H'], 'The first-slot cap convention is unchanged')
    pair_tail = F(quadratic['complete_tail_distinct_pairs'])
    pure_pair = F(7, 10)*complete.geometric(3, 3, 1, -3)
    recorded_partition = old_partition['complete_source_cases'][0]
    require(recorded_partition['sigma'] == recorded_partition['E27'] == '0'
            and all(F(v) == 0 for v in recorded_partition['defects'].values())
            and F(recorded_partition['pair_partition']['weighted_old_pure_blocks_before_halving']['pure3'])/2 == pure_pair
            and F(recorded_partition['pair_partition']['tail_distinct_pairs']) == pair_tail,
            'The128 disjoint old-tail partition allocated exactly this complete pure-three block')
    require(pure_pair == F(7, 360) and pair_tail == factorial_module.PAIR_TAIL_UPPER == F(2539, 3600),
            'Exact complete pure-three unordered-pair block and unchanged other tail classes')
    require(complete.geometric(3, 3, 0, 1) == F(1, 18)
            and complete.geometric(3, 3, 1, -3) == F(1, 36), 'The two complete Bellman reward series')
    require(previous['faces'] == quadratic['faces'] == old_factorial['faces']
            and previous['r'] == previous['rho'] == quadratic['r'] == quadratic['rho'] == '0',
            'The same two complete saturated actual source faces')
    D, L, Q = map(F, (previous['mass'], previous['linear_upper'], previous['complete_square_upper']))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(2203, 450)), 'Consume the171 complete square improvement simultaneously')
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(used.get(path) == pin for path, pin in engine.pins.items()), 'The complete original inventory is pinned')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = list(map(F, previous['improved_cost_bounds'])), list(map(F, previous['cost_weights']))
    require(len(tags) == len(old_costs) == len(weights) == 52, 'All52 independent original costs')
    records = []
    for index in range(41, 52):
        expansion = quad.quadratic_expansion(engine.source, tags[index])
        row = {'index': index, 'tag': tags[index], 'expansion': expansion, 'previous_cost_bound': old_costs[index]}
        if expansion['negative_hinge_coefficients']:
            row['status'] = 'negative-hinge-obstruction'
        else:
            scaling = quad.normalize(expansion)
            objective = mean.prepare(scaling['primitive_hinges'])
            mean_factor = bridge.integer(objective['factor'])
            require(all(mean_factor*objective['primitive_coefficients'][t] == c
                        for t, c in scaling['primitive_hinges'].items()), 'Both normalizations are restored')
            row.update(status='enumerate', scaling=scaling, objective=objective, mean_factor=mean_factor)
        records.append(row)
    active = [r for r in records if r['status'] == 'enumerate']
    require([r['index'] for r in active] == [41, 42, 43, 44, 45, 47, 48, 49, 50, 51], 'Exactly the ten positive expansions')
    total = lcm(mean_module.TOTAL, 21600)
    mean_scale = total//mean_module.TOTAL
    require(total % 21600 == 0, 'Exact common scale includes every new Bellman denominator')
    best, witnesses, ties = {}, {}, {r['index']: 0 for r in active}
    digest, head_digest, old_digest = sha256(), sha256(), sha256()
    count, strict_heads, equal_heads = 0, 0, 0
    best_head, head_witnesses = F(-1), []
    extras = [(r, s, mean.common.extra(r, s)) for r, s in product(range(2), range(5))]
    for li, layout in enumerate(product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))):
        B = bridge.head_load(layout)
        h = problem.components(layout, B)
        require(h['replacement_difference'] <= 0, 'The conditioned replacement never worsens an original layout')
        strict_heads += int(h['adopted_difference'] < 0)
        equal_heads += int(h['adopted_difference'] == 0)
        head_digest.update(json.dumps(encode([layout, h]), separators=(',', ':')).encode())
        old_digest.update(json.dumps([layout, factorial.component_numerators(layout, B)], separators=(',', ':')).encode())
        if h['head_upper'] > best_head:
            best_head, head_witnesses = h['head_upper'], [{'layout': layout, **h}]
        elif h['head_upper'] == best_head:
            head_witnesses.append({'layout': layout, **h})
        correction = bridge.integer(mean_module.TOTAL*mean.correction(layout))
        head_numerator = bridge.integer(total*h['head_upper'])
        for root, slot, extra in extras:
            for row in active:
                index, objective, scaling = row['index'], row['objective'], row['scaling']
                raw, detail = mean.common.objective(objective, B, extra)
                correction_term = objective['primitive_coefficients'].get(1, 0)*correction
                require(raw >= correction_term >= 0, 'Same actual mean-head deletion')
                mean_part = mean_scale*row['mean_factor']*(raw-correction_term)
                factorial_part = scaling['primitive_factorial']*head_numerator
                value = mean_part+factorial_part
                digest.update(json.dumps([li, root, slot, index, value], separators=(',', ':')).encode())
                count += 1
                if index not in best or value > best[index]:
                    best[index], ties[index] = value, 1
                    witnesses[index] = {'layout': layout, 'positive7_root': root, 'positive7_slot': slot,
                                        'scaled_primitive_mean_part': mean_part,
                                        'scaled_primitive_factorial_head_part': factorial_part,
                                        'scaled_mean_correction_before_internal_factor': correction_term,
                                        'joint_factorial_head': h, **detail}
                elif value == best[index]:
                    ties[index] += 1
        if (li+1) % 2500 == 0:
            print('Joint pure-three/factorial heads '+str(li+1)+'/12500', flush=True)
    require(count == 1250000 and strict_heads > 0 and strict_heads+equal_heads == 12500
            and old_digest.hexdigest() == old_factorial['all_layout_components_sha256'], 'Complete original layout scan')
    require(best_head == F(319, 2160) and best_head+pair_tail == F(2303, 2700), 'Strict full factorial-tail improvement')
    direct, results = list(old_costs), []
    for row in records:
        index, expansion = row['index'], row['expansion']
        result = {k: v for k, v in row.items() if k != 'objective'}
        if row['status'] == 'enumerate':
            witness, scaling = witnesses[index], row['scaling']
            layout = witness['layout']
            value, _ = mean.objective(row['objective'], layout, bridge.head_load(layout),
                                     mean.common.extra(witness['positive7_root'], witness['positive7_slot']))
            public = row['mean_factor']*F(value, mean_module.TOTAL)
            public += scaling['primitive_factorial']*problem.components(layout)['head_upper']
            require(public == F(best[index], total), 'Both public head APIs reconstruct each maximum')
            bound = expansion['at_one']*D+scaling['factor']*public+expansion['factorial_tail_coefficient']*pair_tail
            direct[index] = min(old_costs[index], bound)
            result.update(uniform_cost_upper=bound, maximizing_witness=witness, maximizer_count=ties[index])
        result.update(accepted_cost_upper=direct[index], weighted_direct_gain=weights[index]*(old_costs[index]-direct[index]))
        results.append(result)
    require(direct[:41] == old_costs[:41] and direct[46] == old_costs[46], 'All linear and signed-obstruction rows retained')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda v, tag=t: engine.source.zero5_cost(tag, v) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, proofs = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    old_N = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    direct_gain = sum(w*(a-b) for w, a, b in zip(weights, old_costs, direct))
    propagation = sum(w*(a-b) for w, a, b in zip(weights, direct, costs))
    require(old_N == F(previous['numerator_upper']) and old_N-N == direct_gain+propagation
            and direct_gain > 0 and propagation >= 0 and N > 0, 'One complete gain, measured against171')
    denominator = D-F(previous['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in previous['AP11_block_results'])
        +F(previous['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(previous['uniform_denominator_lower']) == F(50511415637, 632754738000) > 0,
            'Every111 AP11 block, complete count tail and AP13 loss remains')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    require(offset+old_N/denominator == F(previous['comparison_upper'])
            and 403 < comparison < F(previous['comparison_upper']), 'A strict complete-face gain, still above403')
    return {'schema': 'erdos7-pure-three-joint-factorial-comparison-v1', 'source_sha256': used,
            'faces': previous['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
            'deep_density_caps': problem.density, 'removed_pure_three_pair_upper': pure_pair,
            'original128_pair_partition': recorded_partition['pair_partition'],
            'complete_tail_distinct_pairs': pair_tail, 'strictly_improved_head_layouts': strict_heads,
            'unchanged_head_layouts': equal_heads, 'head_components_sha256': head_digest.hexdigest(),
            'head_operator_maximum': best_head, 'head_maximizing_witnesses': head_witnesses,
            'second_factorial_tail_upper': best_head+pair_tail,
            'previous_second_factorial_tail_upper': F(prior_factorial['second_factorial_tail_upper']),
            'quadratic_results': results, 'joint_layout_checks': count,
            'joint_objectives_sha256': digest.hexdigest(), 'common_objective_scale': total,
            'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
            'previous_cost_bounds': old_costs, 'direct_cost_upper_bounds': direct, 'majorants': proofs,
            'improved_cost_bounds': costs,
            'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
            'signed_mass_coefficient': signed, 'complete_square_weight': square_weight, 'complete_square_upper': Q,
            'direct_numerator_improvement': direct_gain, 'majorant_propagation_improvement': propagation,
            'total_numerator_improvement_over171': old_N-N, 'previous_numerator': old_N, 'numerator_upper': N,
            'AP11_block_results': previous['AP11_block_results'], 'full_count_tail': previous['full_count_tail'],
            'standalone_hinge4_penalty': F(previous['standalone_hinge4_penalty']),
            'uniform_denominator_lower': denominator, 'offset': offset,
            'previous_comparison': F(previous['comparison_upper']), 'comparison_upper': comparison,
            'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'scope': 'Ordinary uniform comparison on both complete actual saturated K faces, retaining one original head in each cost separately. The pure-three head cross and entire deep-three pair block are bounded jointly, while retaining168 pure-five correction on each same layout. All52 independent costs, every other pair class, full polynomial and geometric tails, the171 square bound and the full111 denominator remain. No off-face extension, new global K, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('five_factorial_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact pure-three joint factorial consumer certificate')
    print('PASS:12500 original heads,1250000 complete quadratic objectives, all52 independent costs.')
    print('Complete face comparison='+str(float(F(result['comparison_upper'])))+
          '; improvement over171='+str(float(F(result['comparison_improvement'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
