#!/usr/bin/env python3
"""Keep one original head across positive hinges and the factorial tail.

The exact quadratic expansion retains its entire polynomial tail. The
one raw81 row with negative hinge coefficients keeps its previous bound.
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
CERTIFICATE = 'certificates/source_norms/whole_quadratic_same_head.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/whole_block_mean_survival.py': 'fbf4823db0269c993745acc4d507fe5734cf8aaff9d12f7f96dcb7ddfd435523',
    'certificates/source_norms/whole_block_mean_survival.json': '909d3aa9ef603b8f066bf64ced71309f51959a6b251781c89f1b7b15f633e5ae',
    'frontier/whole_cost_mean_stop_loss.py': 'ce6fe161966af3c3ee10e837e4b63d40bd079db465c7b8cc9667aa67fe27ab1f',
    'certificates/source_norms/whole_cost_mean_stop_loss.json': 'd535a2f69617536a06655c61a1166813bfd2ce3e17416fc329dcead0ba3201da',
    'frontier/whole_factorial_same_head.py': '65def5c326c9da6dde7de1bfd91c241347aed825e37af8eeda17883dc091c205',
    'certificates/source_norms/whole_factorial_same_head.json': 'cc984cce40af485b438b21f69eeffc7dcfc6978c76bc43a36246ae126d8cb329',
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
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def quadratic_expansion(source, tag):
    """Exact all-load expansion, including a signed obstruction if present."""
    degree, leading, constant, cutoff = source.zero5_cost_metadata(tag)
    require(degree == 2 and leading > 0, 'A complete quadratic polynomial with positive leading coefficient')
    last = max(5, cutoff)
    values = {v: source.zero5_cost(tag, v) for v in range(1, last+4)}
    first, theta = values[1], 2*leading
    coefficients = {1: values[2]-values[1]}
    coefficients.update({t: values[t+1]-2*values[t]+values[t-1]-(theta if t >= 5 else 0)
                         for t in range(2, last+1)})
    phi = lambda v: F(max(v-5, 0)*(v-4), 2)
    expand = lambda v: first+sum(c*max(v-t, 0) for t, c in coefficients.items())+theta*phi(v)
    require(first >= 0 and coefficients[1] >= 0, 'Nonnegative value at one and initial first difference')
    require(all(expand(v) == value for v, value in values.items()), 'Every finite transition of the same original quadratic cost')
    require(sum(coefficients.values())-F(9, 2)*theta == 0
            and first-sum(t*c for t, c in coefficients.items())+10*theta == constant,
            'Both coefficients of the entire polynomial tail match exactly')
    require(all(values[v] == leading*v*v+constant for v in range(cutoff, last+4)), 'Pinned infinite polynomial-tail formula')
    return {'at_one': first, 'hinge_coefficients': coefficients, 'factorial_tail_coefficient': theta,
            'polynomial_tail': {'leading': leading, 'constant': constant, 'entrance': cutoff},
            'negative_hinge_coefficients': {t: c for t, c in coefficients.items() if c < 0},
            'finite_transition_values': values}


def normalize(expansion):
    """One rational factor for every hinge coefficient and the factorial part."""
    hinges = {int(t): F(v) for t, v in expansion['hinge_coefficients'].items() if F(v)}
    theta = F(expansion['factorial_tail_coefficient'])
    require(hinges and theta > 0 and all(1 <= t <= 8 and c > 0 for t, c in hinges.items()),
            'Only the nonnegative supported hinge expansions enter the source operator')
    denominator = lcm(theta.denominator, *(c.denominator for c in hinges.values()))
    integers = {t: int(c*denominator) for t, c in hinges.items()}
    theta_integer = int(theta*denominator)
    divisor = gcd(theta_integer, *integers.values())
    factor = F(divisor, denominator)
    primitive = {t: c//divisor for t, c in integers.items()}
    factorial = theta_integer//divisor
    require(factor*factorial == theta and all(factor*primitive[t] == c for t, c in hinges.items())
            and gcd(factorial, *primitive.values()) == 1, 'Exact primitive joint scaling')
    return {'factor': factor, 'primitive_hinges': primitive, 'primitive_factorial': factorial}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('joint_quad_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = read('certificates/source_norms/whole_block_mean_survival.json')
    factorial_certificate = read('certificates/source_norms/whole_factorial_same_head.json')
    mean_certificate = read('certificates/source_norms/whole_cost_mean_stop_loss.json')
    for prior in (previous, factorial_certificate, mean_certificate):
        for path, pin in prior['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited input: '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited input: '+path)
            used[path] = pin
    stop_loss = read('certificates/source_norms/whole_face_stop_loss_generator.json')
    bridge = module('joint_quad_bridge', base/'frontier/k_face_common_seven_hinges.py')
    common = module('joint_quad_common', base/'frontier/whole_cost_common_stop_loss.py')
    mean_module = module('joint_quad_mean', base/'frontier/whole_cost_mean_stop_loss.py')
    factorial_module = module('joint_quad_factorial', base/'frontier/whole_factorial_same_head.py')
    mean = mean_module.MeanHead(bridge, stop_loss, common)
    factorial = factorial_module.FactorialHead(bridge)
    require(previous['faces'] == factorial_certificate['faces'] == mean_certificate['faces']
            and previous['r'] == previous['rho'] == factorial_certificate['r'] == factorial_certificate['rho'] == '0',
            'The same complete actual saturated K-control faces')
    D, L, Q = map(F, (previous['mass'], previous['linear_upper'], previous['complete_square_upper']))
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(374, 75)), 'Unchanged actual mass and complete moment bounds')
    pair_tail = F(factorial_certificate['complete_tail_distinct_pairs'])
    require(pair_tail == factorial_module.PAIR_TAIL_UPPER == F(2539, 3600)
            and mean_module.TOTAL % factorial_module.HEAD_SCALE == 0, 'Complete pair tail and exact common integer scale')
    factorial_scale = mean_module.TOTAL//factorial_module.HEAD_SCALE
    engine = module('joint_quad_inventory', base/'frontier/source_barrier_saturation.py').Experiment(base)
    require(all(path in used and used[path] == pin for path, pin in engine.pins.items()), 'The whole original52-cost inventory is pinned')
    specs = engine.specs+engine.quadratic_specs
    tags = [spec['tag'] for spec in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(len(tags) == 52, 'All original AP and raw81 cost tags')
    old_costs, weights = list(map(F, previous['improved_cost_bounds'])), list(map(F, previous['cost_weights']))
    records = []
    for index in range(41, 52):
        expansion = quadratic_expansion(engine.source, tags[index])
        row = {'index': index, 'tag': tags[index], 'expansion': expansion,
               'previous_cost_bound': old_costs[index]}
        if expansion['negative_hinge_coefficients']:
            row['status'] = 'negative-hinge-obstruction'
        else:
            scaling = normalize(expansion)
            objective = mean.prepare(scaling['primitive_hinges'])
            mean_factor = bridge.integer(objective['factor'])
            require(all(mean_factor*objective['primitive_coefficients'][t] == c
                        for t, c in scaling['primitive_hinges'].items()), 'Restore the second normalization inside MeanHead')
            row.update({'status': 'enumerate', 'scaling': scaling, 'mean_factor': mean_factor, 'objective': objective})
        records.append(row)
    active = [row for row in records if row['status'] == 'enumerate']
    require([row['index'] for row in active] == [41, 42, 43, 44, 45, 47, 48, 49, 50, 51]
            and records[5]['index'] == 46 and records[5]['expansion']['negative_hinge_coefficients'] == {t: F(-2) for t in range(5, 9)},
            'Exactly ten positive expansions; the original raw81n1 row is retained without invalid sign reversal')
    best, witnesses, ties = {}, {}, {row['index']: 0 for row in active}
    digest, head_digest, count = sha256(), sha256(), 0
    largest_factorial_head = 0
    extras = [(root, slot, mean.common.extra(root, slot)) for root, slot in product(range(2), range(5))]
    for li, layout in enumerate(product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))):
        B = bridge.head_load(layout)
        correction = bridge.integer(mean_module.TOTAL*mean.correction(layout))
        parts = factorial.component_numerators(layout, B)
        factorial_numerator = sum(parts)
        largest_factorial_head = max(largest_factorial_head, factorial_numerator)
        head_digest.update(json.dumps([layout, parts], separators=(',', ':')).encode())
        for root, slot, extra in extras:
            for row in active:
                index, objective, scaling = row['index'], row['objective'], row['scaling']
                raw, detail = mean.common.objective(objective, B, extra)
                correction_term = objective['primitive_coefficients'].get(1, 0)*correction
                require(raw >= correction_term >= 0, 'The same mean head retains its own certified deletion')
                mean_part = row['mean_factor']*(raw-correction_term)
                factorial_part = scaling['primitive_factorial']*factorial_scale*factorial_numerator
                value = mean_part+factorial_part
                digest.update(json.dumps([li, root, slot, index, value], separators=(',', ':')).encode())
                count += 1
                if index not in best or value > best[index]:
                    best[index], ties[index] = value, 1
                    witnesses[index] = {'layout': layout, 'positive7_root': root, 'positive7_slot': slot,
                                        'scaled_primitive_mean_part': mean_part,
                                        'scaled_primitive_factorial_head_part': factorial_part,
                                        'scaled_mean_correction_before_internal_factor': correction_term,
                                        'factorial_head_component_numerators': parts, **detail}
                elif value == best[index]:
                    ties[index] += 1
        if (li+1) % 2500 == 0:
            print('Joint quadratic/factorial heads '+str(li+1)+'/12500', flush=True)
    require(count == 1250000 and head_digest.hexdigest() == factorial_certificate['all_layout_components_sha256']
            and F(largest_factorial_head, factorial_module.HEAD_SCALE) == F(factorial_certificate['head_operator_maximum']),
            'All ten new joint objectives use the identical112 factorial-head table')
    direct, results = list(old_costs), []
    for row in records:
        index, expansion = row['index'], row['expansion']
        result = {k: v for k, v in row.items() if k != 'objective'}
        if row['status'] == 'enumerate':
            witness, scaling = witnesses[index], row['scaling']
            layout = witness['layout']
            value, _ = mean.objective(row['objective'], layout, bridge.head_load(layout),
                                       mean.common.extra(witness['positive7_root'], witness['positive7_slot']))
            public_value = row['mean_factor']*F(value, mean_module.TOTAL)
            public_value += scaling['primitive_factorial']*factorial.factorial_head_bound(layout)
            require(public_value == F(best[index], mean_module.TOTAL), 'Both public same-head APIs reproduce the saved maximum')
            bound = expansion['at_one']*D+scaling['factor']*public_value+expansion['factorial_tail_coefficient']*pair_tail
            direct[index] = min(old_costs[index], bound)
            result.update({'uniform_cost_upper': bound, 'maximizing_witness': witness, 'maximizer_count': ties[index]})
        result['accepted_cost_upper'] = direct[index]
        result['weighted_direct_gain'] = weights[index]*(old_costs[index]-direct[index])
        results.append(result)
    require(direct[:41] == old_costs[:41] and direct[46] == old_costs[46], 'All109 linear bounds and the signed-obstruction row remain')
    consumer = module('joint_quad_consumer', base/'frontier/vector_face_complete_ratio.py')
    majorant = module('joint_quad_majorant', base/'frontier/endpoint_numerator_common_costs.py')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda v, tag=tag: engine.source.zero5_cost(tag, v) for tag in all_tags]
    metadata = [engine.source.zero5_cost_metadata(tag) for tag in all_tags]
    costs, proofs = consumer.propagate(majorant, functions, metadata, direct, old_costs, D, L, Q)
    signed, square_weight = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    require(len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight,
            'All original signed numerator terms and both square complements retained')
    old_N = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    direct_gain = sum(w*(a-b) for w, a, b in zip(weights, old_costs, direct))
    propagation = sum(w*(a-b) for w, a, b in zip(weights, direct, costs))
    require(old_N == F(previous['numerator_upper']) and old_N-N == direct_gain+propagation
            and direct_gain > 0 and propagation >= 0 and N > 0, 'Every new complete numerator gain is counted once')
    tail = previous['full_count_tail']
    denominator = D-F(previous['standalone_hinge4_penalty'])-(sum(F(r['joint_mean_upper']) for r in previous['block_results'])
                  +F(tail['remaining_cost_upper']))/7
    require(denominator == F(previous['uniform_denominator_lower']) == F(50511415637, 632754738000),
            'All four111 original AP11 blocks, every count tail and the independent AP13 loss retained')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    require(offset+old_N/denominator == F(previous['comparison_upper']) and 403 < comparison < F(previous['comparison_upper']),
            'Strict same-denominator whole-face improvement still above403')
    return {'schema': 'erdos7-whole-quadratic-same-head-v1', 'source_sha256': used,
            'faces': previous['faces'], 'mass': D, 'r': F(0), 'rho': F(0), 'linear_upper': L,
            'quadratic_results': results, 'joint_layout_checks': count, 'joint_objectives_sha256': digest.hexdigest(),
            'factorial_head_scale': factorial_module.HEAD_SCALE, 'common_objective_scale': mean_module.TOTAL,
            'factorial_head_components_sha256': head_digest.hexdigest(), 'complete_tail_distinct_pairs': pair_tail,
            'cost_weights': weights, 'direct_cost_upper_bounds': direct, 'majorants': proofs, 'improved_cost_bounds': costs,
            'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
            'signed_mass_coefficient': signed, 'complete_square_weight': square_weight, 'complete_square_upper': Q,
            'direct_numerator_improvement_over111': direct_gain, 'majorant_propagation_improvement': propagation,
            'total_numerator_improvement_over111': old_N-N, 'previous_numerator': old_N, 'numerator_upper': N,
            'AP11_block_results': previous['block_results'], 'full_count_tail': tail,
            'standalone_hinge4_penalty': F(previous['standalone_hinge4_penalty']),
            'uniform_denominator_lower': denominator, 'offset': offset, 'previous_comparison': F(previous['comparison_upper']),
            'comparison_upper': comparison, 'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'scope': 'Ordinary uniform result on both complete actual saturated K faces. Positive hinge terms and the whole factorial head of each original quadratic cost use one original layout; different cost tests remain independent. Complete polynomial tails, all old/seven pair complements, all52 signed costs and the whole111 denominator are retained. The raw81n1 row with negative middle hinges keeps its old bound. No off-face extension, new global K, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('joint_quad_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact canonical same-head quadratic certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: ten positive quadratic expansions,1250000 same-head objectives, complete52-cost numerator and111 denominator.')
    print('Comparison '+str(float(F(result['comparison_upper'])))+'; numerator gain '+str(float(F(result['total_numerator_improvement_over111'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
