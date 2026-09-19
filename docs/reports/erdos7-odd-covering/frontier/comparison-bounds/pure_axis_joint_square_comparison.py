#!/usr/bin/env python3
"""Keep the shallow pure3/pure5 choices in their complete joint square block."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/pure_axis_joint_square_comparison.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/moments-survival/pure_three_joint_factorial_comparison.py': '135c77770cfb09752ff9ab82508ddd1e377f49b5ec783d8e85d2d7638cb0cef8',
    'certificates/source_norms/moments-survival/pure_three_joint_factorial_comparison.json': 'cd6f257de24931fc8aa0ecc2bf95e87ad4327cc72b77c401a325572dca22f3c6',
    'frontier/cover-geometry/pure_axis_cross_sharpness.py': '6d5fd1228ae82ffef81e117d7d19d7a7cfd6eb7609764f805ff900d10b802bb1',
    'certificates/source_norms/cover-geometry/pure_axis_cross_sharpness.json': 'e1e9de1d112f4bc84fbb5d73a06650b70599d40dc4f0e0cc3e87536b760eaa3d',
    'frontier/moments-survival/whole_factorial_same_head.py': '02b5af74e00afc26b940d8c6b485fbea654a4d2f9dd52d986875c303a79faacd',
    'frontier/endpoint-bounds/k_face_common_seven_hinges.py': '3128cab9f43ad9c89a5f129b7c7d0115a6f73684f613111a07a56f0bd71ddcdd',
    'frontier/moments-survival/pure_three_joint_moments.py': 'dcd5dae8b9ff0ef9c79f7ad7a52183079226815d2bf229f3ebcae349b9d70351',
    'frontier/moments-survival/pure_five_joint_moments.py': 'ce2e635e296e720d241fa413ab18efe8cbeb4c2f80ecdc21e25573ee728d1ea7',
    'profile-notes/065-128/128-the-complete-factorial-tail-retains-its-head-off-the-face.md': '79ae5ce60d7121afdc3fe0eaa3a87abecf21709d15e7627c2425dd7bdb4926cc',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable existing proof input')
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


def bellman_support(alpha, beta, prime, first_depth):
    """Exact affine-potential identities used in the arbitrary-path proof."""
    q = F(1, prime)
    require(len(alpha) == len(beta) == 5 and min(alpha+beta) >= 0,
            'Nonnegative reward and repeat-count slope for every independently chosen cell')
    intercept = tuple(a/(1-q)+b*q/(1-q)**2 for a, b in zip(alpha, beta))
    slope = tuple(b/(1-q) for b in beta)
    for a, b, u, v in zip(alpha, beta, intercept, slope):
        require((1-q)*u == a+q*v and (1-q)*v == b and (1-q)*u >= a,
                'All-count same-cell identity and different-cell Bellman inequality')
    return {'prime': prime, 'first_depth': first_depth, 'initial_reward': alpha,
            'repeat_reward': beta, 'potential_intercept': intercept,
            'potential_count_slope': slope,
            'complete_candidates': tuple(q**first_depth*v for v in intercept)}


def candidate_rows(bridge, table, three, five):
    ROOT, c3, c5 = bridge.ROOT, three.DENSITY, five.DENSITY
    require(ROOT == three.ROOT == (0, 0, 1, 1, 1)
            and c3 == (F(7, 10), F(11, 20), F(3, 10), F(3, 10), F(3, 10))
            and c5 == (F(0), F(2, 15), F(14, 45), F(2, 5), F(7, 30))
            and five.FIRST == (F(0), F(2, 75), F(14, 225), F(7, 150), F(7, 150)),
            'Only the existing171 and164 proved marginal inputs')
    require(all(0 <= table.w[c][s] <= 1 for c, s in product(range(5), repeat=2)),
            'Pointwise selected-source weights are nonnegative and bounded by Haar')
    ac = tuple(max(table.w[c][s] for s in range(5) if table.pre[c][s] > 0) for c in range(5))
    require(ac == (F(1), F(4, 5), F(4, 5), F(4, 5), F(4, 5)),
            'Exact allowed-slot maxima for the deep3/deep5 cross, with excluded slots absent')
    rows = []
    for root, cell, first in product(range(2), range(5), range(5)):
        n = tuple(int(ROOT[c] == root)+int(c == cell) for c in range(5))
        shallow3 = 3*three.FIRST[root]+(3+2*int(ROOT[cell] == root))*three.SECOND[cell]
        first_cross = sum(table.head_caps[c][first] for c in range(5) if ROOT[c] == root)+table.head_caps[cell][first]
        H = tuple(sum(table.descendant[c][s]*table.w[c][s] for c in range(5) if ROOT[c] == root)
                  +table.descendant[cell][s]*table.w[cell][s] for s in range(5))
        alpha3 = tuple(c3[c]*(3+2*n[c])+2*table.pre[c][first]*table.w[c][first]+ac[c]/10 for c in range(5))
        alpha5 = tuple(c5[s]*(3+2*int(s == first))+2*H[s] for s in range(5))
        b3 = bellman_support(alpha3, tuple(2*v for v in c3), 3, 3)
        b5 = bellman_support(alpha5, tuple(2*v for v in c5), 5, 2)
        deep3 = tuple((c3[c]*(n[c]+2)+table.pre[c][first]*table.w[c][first]+ac[c]/20)/9 for c in range(5))
        deep5 = tuple(c5[s]*F(11 if s == first else 7, 40)+H[s]/10 for s in range(5))
        require(b3['complete_candidates'] == deep3 and b5['complete_candidates'] == deep5,
                'The two complete Bellman sums equal their analytic all-depth expressions')
        upper = shallow3+3*five.FIRST[first]+2*first_cross+max(deep3)+max(deep5)
        rows.append({'shallow_three_root': root, 'shallow_three_cell': cell, 'first_five_slot': first,
                     'shallow_three_counts': n, 'shallow_three_moment': shallow3,
                     'first_five_moment': 3*five.FIRST[first], 'shallow_cross': first_cross,
                     'shallow_three_deep_five_coefficients': H,
                     'three_bellman': b3, 'five_bellman': b5,
                     'deep_three_joint': max(deep3), 'deep_five_joint': max(deep5), 'joint_upper': upper})
    require(len(rows) == 50, 'Every independent root, cell and first-five choice')
    best = max(row['joint_upper'] for row in rows)
    witnesses = [row for row in rows if row['joint_upper'] == best]
    require(best == F(1567, 1350) and len(witnesses) == 1
            and tuple(witnesses[0][k] for k in ('shallow_three_root', 'shallow_three_cell', 'first_five_slot')) == (0, 1, 2),
            'Exact complete50-case upper and its relaxed maximizing shallow choice')
    return {'allowed_deep_cross_weights': ac, 'candidate_rows': rows,
            'joint_upper': best, 'maximizing_shallow_choices': [(0, 1, 2)]}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('axis_joint_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior, cross = read('pure_three_joint_factorial_comparison'), read('pure_axis_cross_sharpness')
    pins = dict(PINS)
    for data in (prior, cross):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent actual source closure '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned proof input '+path)
    load = lambda name: module('axis_joint_'+name, io.named_artifact(base/'frontier', name+'.py'))
    bridge, factorial = load('k_face_common_seven_hinges'), load('whole_factorial_same_head')
    three, five = load('pure_three_joint_moments'), load('pure_five_joint_moments')
    table = factorial.FactorialHead(bridge)
    joint = candidate_rows(bridge, table, three, five)
    old_block = three.envelope(F(2))+five.envelope(F(2))+F(cross['ordered_cross_upper'])
    saving = old_block-joint['joint_upper']
    require(old_block == F(539, 450) and saving == F(1, 27), 'Replace the previous two marginal blocks and cross jointly, once')
    D, L, oldQ = (F(prior[k]) for k in ('mass', 'linear_upper', 'complete_square_upper'))
    require((D, L, oldQ) == (F(53, 360), F(1151, 1800), F(2203, 450))
            and prior['r'] == prior['rho'] == '0', 'Same complete saturated actual faces and174 full vector')
    Q = oldQ-saving
    require(Q == F(6559, 1350), 'Every other original LCM category remains in the complete square')
    engine = load('source_barrier_saturation').Experiment(base)
    require(all(pins.get(path) == h for path, h in engine.pins.items()), 'Complete original52-cost inputs')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    old_costs, weights = (list(map(F, prior[k])) for k in ('improved_cost_bounds', 'cost_weights'))
    require(len(tags) == len(old_costs) == len(weights) == 52, 'Every independent original cost')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda v, tag=t: engine.source.zero5_cost(tag, v) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    costs, majorants = load('vector_face_complete_ratio').propagate(
        load('endpoint_numerator_common_costs'), functions, metadata, old_costs, old_costs, D, L, Q)
    signed, square_weight = (F(prior[k]) for k in ('signed_mass_coefficient', 'complete_square_weight'))
    require(square_weight > 0, 'The complete square has its original positive consumer weight')
    oldN = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*oldQ
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    propagation = sum(w*(a-b) for w, a, b in zip(weights, old_costs, costs))
    require(oldN == F(prior['numerator_upper']) and oldN-N == square_weight*saving+propagation
            and all(0 <= b <= a for a, b in zip(old_costs, costs)) and propagation >= 0 and N > 0,
            'One complete numerator with every current174 factorial improvement retained')
    denominator = D-F(prior['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in prior['AP11_block_results'])
        +F(prior['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(prior['uniform_denominator_lower']) == F(50511415637, 632754738000) > 0,
            'Every original AP11 block, AP13 loss and infinite count tail remains')
    offset = F(prior['offset'])
    comparison = offset+N/denominator
    require(offset+oldN/denominator == F(prior['comparison_upper'])
            and 403 < comparison < F(prior['comparison_upper']), 'Strict complete-face improvement, still above403')
    return encode({'schema': 'erdos7-pure-axis-joint-square-comparison-v1', 'source_sha256': pins,
                   'faces': prior['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
                   'root_caps': three.FIRST, 'cell_caps': three.SECOND,
                   'first_five_caps': five.FIRST, 'deep_three_caps': three.DENSITY, 'deep_five_caps': five.DENSITY,
                   'source_pre': table.pre, 'source_descendant': table.descendant,
                   'selected_density_weights': table.w, 'rectangle_caps': table.head_caps,
                   'joint_moment': joint, 'previous_pure_axis_block': old_block,
                   'complete_square_saving': saving, 'previous_complete_square_upper': oldQ, 'complete_square_upper': Q,
                   'all_original_indices': list(range(52)), 'original_cost_tags': tags, 'cost_weights': weights,
                   'previous_cost_bounds': old_costs, 'improved_cost_bounds': costs, 'majorants': majorants,
                   'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
                   'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
                   'direct_numerator_improvement': square_weight*saving,
                   'majorant_propagation_improvement': propagation, 'numerator_upper': N,
                   'AP11_block_results': prior['AP11_block_results'], 'full_count_tail': prior['full_count_tail'],
                   'standalone_hinge4_penalty': F(prior['standalone_hinge4_penalty']),
                   'uniform_denominator_lower': denominator, 'offset': offset,
                   'previous_comparison': F(prior['comparison_upper']), 'comparison_upper': comparison,
                   'comparison_improvement': F(prior['comparison_upper'])-comparison,
                   'scope': 'Ordinary joint complete pure3/pure5 square-block bound and full52-cost comparison on both actual saturated K faces. The same shallow root, cell and first-five slot remain in both Bellman rewards. Deep3/deep5 cross is allocated once to the three path using actual pointwise source domination. All174 factorial gains, every other LCM pair class and all infinite tails/denominator terms remain. No actual-family sharpness, off-face/global extension, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('axis_joint_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact joint pure-axis comparison certificate')
    print('PASS: all50 joint shallow choices; full square<=6559/1350; complete face='+result['comparison_upper'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
