#!/usr/bin/env python3
"""Complete survivor-first stop-loss bounds and their 52-cost face consumer.

Five new integer-threshold objectives reuse the original six-label head,
source LP and selected-cylinder operators. Fourth/fifth hinges reuse the
already certified identical surviving-tail formulas. All tails are whole.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/whole_face_stop_loss_generator.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/endpoint-bounds/vector_face_complete_ratio.py': 'fa0387a38436b575628c850099e4826ded791613c4cf150793b56d7c03e3427f',
    'certificates/source_norms/endpoint-bounds/vector_face_complete_ratio.json': 'e5a4781cb7eed36ce862f06d099bfefa296d45c1391edbe2b81db2d437130dc5',
    'frontier/endpoint-bounds/k_face_common_seven_hinges.py': '3128cab9f43ad9c89a5f129b7c7d0115a6f73684f613111a07a56f0bd71ddcdd',
    'certificates/source_norms/endpoint-bounds/k_face_common_seven_hinges.json': '3acdaa029a606ff79e483294f52390a0fed1df0ddbf444f5b42e1c982ca1d8eb',
    'frontier/endpoint-bounds/k_face_surviving_tail_ratio.py': '8939d32f56b42c7d02dbafbf316fdd3c79160d47f3190cc50badbc2277ad5096',
    'certificates/source_norms/endpoint-bounds/k_face_surviving_tail_ratio.json': 'b9c283262fd9c06798d4082f30da570d97926c271768e4790f94be7c6e70cb09',
}
NEW_THRESHOLDS = (2, 3, 6, 7, 8)
COST_SCALE = 5*7**7
TOTAL_SCALE = COST_SCALE*16200


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module: '+str(path))
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


def stop_loss_profile(bridge, old_hinges, survivor):
    pre, raw, w, descendant = bridge.source_tables(2)
    require(encode(raw) == old_hinges['source_upper_table'] and encode(w) == old_hinges['retained_density']
            and encode(descendant) == old_hinges['raw_descendant5_coefficients'], 'The full original source tables')
    for first in (2, 3, 4):
        other = bridge.source_tables(first)
        perm = list(range(5))
        perm[2], perm[first] = perm[first], perm[2]
        require(all(all(canonical[c] == moved[perm[c]] for c in range(5))
                    for canonical, moved in zip((pre, raw, w, descendant), other))
                and tuple(bridge.ROOT[c] for c in perm) == bridge.ROOT, 'Every first-beta table has the same complete source and tail program')
    caps = [bridge.integer(360*x) for row in raw for x in row]
    budgets = [bridge.integer(360*x) for x in bridge.GROUP_MASSES]
    require(bridge.GROUP_MASSES == (F(1, 36), F(1, 12), F(5, 36)), 'Exact complete root1 beta budget')
    p = [[bridge.integer(20*x) for x in row] for row in pre]
    q = [[bridge.integer(18*x) for x in row] for row in descendant]
    wi = [bridge.integer(5*x) for row in w for x in row]
    require(min(wi) >= 2 and bridge.ORDER == ((0, 2), (3, 0), (1, 2), (4, 0)), 'Same positive density and25,27,75,81 order')
    costs, convex_checks = {}, 0
    for t, weight, extra in product(range(1, 9), sorted(set(wi)), range(3)):
        values = [F(weight, 5)*max(v-t, 0)+bridge.seven_increment(t, v, extra) for v in range(1, 12)]
        increments = [b-a for a, b in zip(values, values[1:])]
        require(min(increments) >= 0 and all(a <= b for a, b in zip(increments, increments[1:])), 'Increasing integer-convex bridge for every used threshold')
        require(all(x == F(weight, 5) for x in increments[t-1:]), 'Exact complete affine bridge tail')
        costs[t, weight, extra] = [0]+[bridge.integer(COST_SCALE*v) for v in values]
        convex_checks += 1

    def tail_scaled(coefficients, a, b):
        require(min(coefficients) >= 0, 'Every selected-cylinder objective is nonnegative')
        if b == 0:
            require(a in (3, 4), 'Original selected pure3 cylinders')
            value = max(sum(p[c][s]*coefficients[5*c+s] for s in range(5)) for c in range(5))
            return (16200//(20*3**a))*value
        require(b == 2 and a in (0, 1), 'Original selected descendant-five cylinders')
        if a == 0:
            value = max(sum(q[c][s]*coefficients[5*c+s] for c in range(5)) for s in range(5))
        else:
            value = max(sum(q[c][s]*coefficients[5*c+s] for c in range(5) if bridge.ROOT[c] == r)
                        for r, s in product(range(2), range(5)))
        return 36*value

    total_old = F(survivor['complete_surviving_old_tail'])
    selected_caps = [F(survivor['selected_surviving_cylinder_caps'][str(n)]) for n in (25, 27, 75, 81)]
    require(total_old == F(163, 1800) and selected_caps == [F(2, 125), F(7, 270), F(4, 375), F(7, 810)],
            'Actual surviving caps, including every old exponent tail')
    positive_tail = F(old_hinges['remaining_positive7'])
    require(positive_tail == F(779, 12600), 'Entire complementary positive-seven family')
    prefixes = {t: min(t-1, 4) for t in range(2, 9)}
    remainders = {t: total_old-sum(selected_caps[:prefixes[t]]) for t in range(2, 9)}
    require(remainders[4] == F(survivor['surviving_old_remainders']['4'])
            and remainders[5] == F(survivor['surviving_old_remainders']['5']), 'Fourth/fifth formulas are exactly the certified86 formulas')
    constants = {t: bridge.integer(TOTAL_SCALE*(positive_tail+remainders[t])) for t in NEW_THRESHOLDS}
    extras = [(root, slot, [int(bridge.ROOT[c] == root)+int(s == slot) for c, s in product(range(5), repeat=2)])
              for root, slot in product(range(2), range(5))]
    best, witnesses, ties = {}, {}, {t: 0 for t in NEW_THRESHOLDS}
    digest, count = sha256(), 0
    for li, layout in enumerate(product(range(2), range(5), range(5), range(2), range(5), range(5), range(5))):
        B = bridge.head_load(layout)
        require(min(B) >= 1 and max(B) <= 6, 'The complete original six-label head')
        for root, slot, extra in extras:
            for t in NEW_THRESHOLDS:
                arrays = [costs[t, weight, ex] for weight, ex in zip(wi, extra)]
                coefficients = [array[v] for array, v in zip(arrays, B)]
                head, dual = bridge.lp_bound(coefficients, caps, budgets)
                selected = [tail_scaled([array[v+i]-array[v+i-1] for array, v in zip(arrays, B)], a, b)
                            for i, (a, b) in enumerate(bridge.ORDER[:prefixes[t]], 1)]
                value = constants[t]+45*head+sum(selected)
                digest.update(json.dumps([li, root, slot, t, head, selected, value], separators=(',', ':')).encode())
                count += 1
                if t not in best or value > best[t]:
                    best[t], ties[t] = value, 1
                    witnesses[t] = {'layout': layout, 'positive7_root': root, 'positive7_slot': slot,
                                    'source_head_lp': F(head, 360*COST_SCALE),
                                    'selected_cylinder_increments': [F(x, TOTAL_SCALE) for x in selected],
                                    'source_head_dual': dual}
                elif value == best[t]:
                    ties[t] += 1
    require(count == 625000, 'All12500 original heads,10 independent positive7 projections and five new thresholds')
    D, L = F(survivor['mass']), F(survivor['linear_upper'])
    uppers = {1: L-D, **{t: F(best[t], TOTAL_SCALE) for t in NEW_THRESHOLDS},
              **{t: F(survivor['uniform_hinge_uppers'][str(t)]) for t in (4, 5)}}
    require(uppers[1] == F(443, 900) and all(0 < uppers[t+1] <= uppers[t] for t in range(1, 8)), 'Complete decreasing stop-loss profile')
    for t in NEW_THRESHOLDS:
        row = witnesses[t]
        require(row['source_head_lp']+sum(row['selected_cylinder_increments'])+remainders[t]+positive_tail == uppers[t],
                'Reconstruct every exact exhaustive maximum with complete remainders')
    return {'uniform_hinge_uppers': uppers, 'selected_prefix_lengths': prefixes,
            'complete_surviving_old_tail': total_old, 'selected_surviving_caps': selected_caps,
            'surviving_old_remainders': remainders, 'complete_complementary_positive7_tail': positive_tail,
            'source_group_masses': bridge.GROUP_MASSES, 'source_upper_table': raw,
            'retained_density': w, 'descendant5_coefficients': descendant,
            'bridge_convexity_checks': convex_checks, 'integer_cost_scale': COST_SCALE,
            'integer_total_scale': TOTAL_SCALE, 'new_layout_checks': count,
            'all_new_layout_values_sha256': digest.hexdigest(), 'maximizing_witnesses': witnesses,
            'maximizer_counts': ties, 'reused_thresholds': [4, 5],
            'reused_layout_sha256': survivor['reused_all_layout_and_dual_sha256']}


def linear_cost_profile(source, tag, D, uppers):
    degree, slope, offset, cutoff = source.zero5_cost_metadata(tag)
    require(degree == 1 and cutoff <= 8 and slope >= 0, 'Complete linear-growth cost is affine by load8')
    values = [source.zero5_cost(tag, v) for v in range(1, 11)]
    require(all(values[v-1] == slope*v+offset for v in range(cutoff, 11)), 'The pinned exact affine tail formula')
    first, delta = values[0], values[1]-values[0]
    curvature = {j: values[j]-2*values[j-1]+values[j-2] for j in range(2, 9)}
    require(delta >= 0 and min(curvature.values()) >= 0, 'Every stop-loss multiplier is nonnegative')
    def reconstruct(v):
        return first+delta*(v-1)+sum(k*max(v-j, 0) for j, k in curvature.items())
    require(all(reconstruct(v) == values[v-1] for v in range(1, 11)), 'Exact finite integer stop-loss expansion')
    require(delta+sum(curvature.values()) == slope
            and first-delta-sum(j*k for j, k in curvature.items()) == offset,
            'Exact infinite affine tail of the same expansion')
    bound = first*D+delta*uppers[1]+sum(k*uppers[j] for j, k in curvature.items())
    return {'at_one': first, 'first_difference': delta, 'curvatures': curvature,
            'affine_tail': {'slope': slope, 'offset': offset, 'entrance': cutoff}, 'cost_upper': bound}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('stop_loss_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = read('certificates/source_norms/endpoint-bounds/vector_face_complete_ratio.json')
    survivor = read('certificates/source_norms/endpoint-bounds/k_face_surviving_tail_ratio.json')
    old_hinges = read('certificates/source_norms/endpoint-bounds/k_face_common_seven_hinges.json')
    for record in (previous, survivor, old_hinges):
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited pin: '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited input: '+path)
            used[path] = pin
    old84 = read('certificates/source_norms/endpoint-bounds/k_face_complete_ratio.json')
    bridge = module('stop_loss_bridge', base/'frontier/endpoint-bounds/k_face_common_seven_hinges.py')
    profile = stop_loss_profile(bridge, old_hinges, survivor)
    engine = module('stop_loss_engine', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    source, specs = engine.source, engine.specs+engine.quadratic_specs
    require(all(path in used and used[path] == pin for path, pin in engine.pins.items()), 'All cost-inventory inputs are pinned')
    consumer = module('stop_loss_consumer', base/'frontier/endpoint-bounds/vector_face_complete_ratio.py')
    majorant = module('stop_loss_majorant', base/'frontier/endpoint-bounds/endpoint_numerator_common_costs.py')
    D, L, Q = F(previous['mass']), F(previous['linear_upper']), F(previous['square_sums']['full_square_upper'])
    require((D, L, Q) == (F(53, 360), F(1151, 1800), F(374, 75)) and previous['r'] == previous['rho'] == '0', 'Same exact saturated face, moments and zero residual')
    weights = list(map(F, previous['cost_weights']))
    old_costs = list(map(F, previous['improved_cost_bounds']))
    direct, updates = list(old_costs), []
    baseline86_costs = list(map(F, old84['improved_cost_bounds']))
    oracle_baseline_gain = F(0)
    for i, spec in enumerate(engine.specs):
        expansion = linear_cost_profile(source, spec['tag'], D, profile['uniform_hinge_uppers'])
        bound = expansion['cost_upper']
        direct[i] = min(old_costs[i], bound)
        oracle_baseline_gain += weights[i]*(baseline86_costs[i]-min(baseline86_costs[i], bound))
        updates.append({'index': i, 'name': spec['name'], 'tuple': spec['tuple'], 'weight': weights[i],
                        'expansion': expansion, 'previous_cost_bound': old_costs[i], 'accepted_cost_bound': direct[i],
                        'weighted_direct_improvement': weights[i]*(old_costs[i]-direct[i])})
    require(len(old_costs) == len(direct) == len(weights) == 52 and direct[41:] == old_costs[41:],
            'Every quadratic and raw81 bound already proved by97 is retained at the direct stage')
    tags = [('h', F(0)), ('s', F(0))]+[spec['tag'] for spec in specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    functions = [lambda n, tag=tag: source.zero5_cost(tag, n) for tag in tags]
    metadata = [source.zero5_cost_metadata(tag) for tag in tags]
    costs, proofs = consumer.propagate(majorant, functions, metadata, direct, old_costs, D, L, Q)
    residual, square_weight = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    require(residual < 0 < square_weight and min(weights) > 0, 'Every signed coefficient is preserved')
    old_N = residual*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Q
    N = residual*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    direct_gain = sum(w*(a-b) for w, a, b in zip(weights, old_costs, direct))
    propagated_gain = sum(w*(a-b) for w, a, b in zip(weights, direct, costs))
    require(old_N == F(previous['numerator_upper']) and old_N-N == direct_gain+propagated_gain
            and direct_gain > 0 and propagated_gain >= 0 and N > 0, 'Complete signed numerator and disjoint improvement balance')
    denominator = consumer.verify_denominator(survivor, old84)
    require(denominator == F(previous['uniform_denominator_lower']), 'Retain97 complete AP11 denominator')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    require(403 < comparison < F(previous['comparison_upper']), 'Whole-face improvement still above the sufficient target')
    return {'schema': 'erdos7-whole-face-stop-loss-generator-v1', 'source_sha256': used,
            'faces': previous['faces'], 'mass': D, 'r': F(0), 'rho': F(0),
            'stop_loss_profile': profile, 'linear_cost_updates': updates,
            'cost_weights': weights, 'direct_cost_bounds': direct, 'majorants': proofs, 'improved_cost_bounds': costs,
            'linear_upper': L, 'square_sums': previous['square_sums'],
            'signed_mass_coefficient': residual, 'complete_square_weight': square_weight,
            'direct_numerator_improvement_over97': direct_gain, 'majorant_propagation_improvement': propagated_gain,
            'total_numerator_improvement_over97': old_N-N, 'stop_loss_only_linear_gain_over86': oracle_baseline_gain,
            'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
            'previous_numerator': old_N, 'numerator_upper': N,
            'uniform_denominator_lower': denominator, 'full_AP11_tail': previous['full_AP11_tail'],
            'denominator_coefficients': previous['denominator_coefficients'], 'offset': offset,
            'previous_comparison': F(previous['comparison_upper']), 'comparison_upper': comparison,
            'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'scope': 'Ordinary full-tail theorem on both complete actual K-control faces with r=rho=0 and exact saturated mass53/360. Independent original residues, all beta distributions permitted by the first-beta source condition. Complete stop-loss generator plus97 vector bounds, all52 costs, one simultaneous majorant substitution and the unchanged full AP11 denominator. No off-face neighborhood, new global K, Lean verification or unrestricted Erdos7 solution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('stop_loss_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical whole-face stop-loss certificate')
    elif args.write or args.output is not None:
        io.write_certificate_text(args.output or args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    else:
        print(json.dumps(result, indent=2))
    print('PASS: complete stop-loss generator,625000 exact new layout/LP checks, all41 affine expansions,52 costs and complete signed/tail comparison.')
    print('Hinges '+str(result['stop_loss_profile']['uniform_hinge_uppers'])+'; comparison '+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
