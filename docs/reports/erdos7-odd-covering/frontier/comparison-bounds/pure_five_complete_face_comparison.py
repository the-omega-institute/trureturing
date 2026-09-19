#!/usr/bin/env python3
"""Consume the sharp pure-five joint moments in the complete face comparison.

Only the zero-seven, zero-three nonunit LCM category changes. All52
original costs, every other square category and the full denominator stay.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import product
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/pure_five_complete_face_comparison.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/moments-survival/whole_quadratic_same_head.py': '84d7995521352aebd522659d189081eee31dbd200ccb4b1f638e7881d3c145b7',
    'certificates/source_norms/moments-survival/whole_quadratic_same_head.json': 'c0f131821927a5aaa8e6e4f1b9fa7ed972ee3c5481e78ff39234f2653a25704f',
    'frontier/moments-survival/pure_five_joint_moments.py': '4d2491befab31bd869fdf037677ea796f40c9941d1d90fbf752fb1c396913306',
    'certificates/source_norms/moments-survival/pure_five_joint_moments.json': 'e17242d61ea209ce8c26538f71acc041ef0ab8f5e29e4e5e5f3930ce991fc2d2',
    'frontier/cover-geometry/uniform_square_and_raw81_neighborhood.py': '3d47bd0d7ff5f5c4f8114d02538073de8bc87e455265817e9e9d80ca4bc5a62c',
    'frontier/endpoint-bounds/vector_face_complete_ratio.py': '08aa9c7a84e48e3ff90cc4baf1bcc918ee70deb551aed8de3480214ee39823c6',
    'frontier/endpoint-bounds/endpoint_numerator_common_costs.py': '1b665058c35f8aaadc60d4513939e6c4255cff212b6289d8c0e3beb7bd1d02d6',
    'frontier/source-budgets/source_barrier_saturation.py': '6fe57e39274df1fa4a80ae4d4a22cab7b1d78d28c4f428b789071e3fb7776a64',
    'frontier/comparison-bounds/uniform_k_neighborhood_cost.py': '365265347aca1ee5a179df991be2316219f0cb4dbe7a5606a020664c3a56723b',
    'frontier/moments-survival/uniform_ap_survival_denominator.py': '181a1793bd15059074d2998eb820322a3b9c2158bac5edfcb3bc057b7e78f180',
    'frontier/moments-survival/complete_off_face_factorial_tail.py': '6f09199dd8379336bbc84e4245c3ea95a0499939cf72a2c41b9ef7b658049498',
    'frontier/cover-geometry/complete_off_face_omitted_tails.py': '33e8c164c64790483ba512c984e8090cf5c44b92bf6ca1cb08a17cb56a93201d',
    'frontier/retained-transport/uniform_shallow_indicator_transport.py': 'c30be3b622143fbd629eed504642faede14664abbfc393c0d1a93246e087a765',
    'certificates/source_norms/retained-transport/uniform_shallow_indicator_transport.json': '07c1562ec4ef340c70dfa30c7b4e427d16d19e8e28190c09abb450f44c2ab0ee',
    'frontier/comparison-bounds/residual_shell_k_comparison.py': '172e74c59a974c25ec9e77b4ee7cd2d4c84ac314f3cca4e3906160a7b065034b',
    'certificates/source_norms/comparison-bounds/residual_shell_k_comparison.json': '1e1b972b2756007c1f259232d4d03c49b527d5e88242b98e4300f48c3fa08f2f',
    'frontier/source-budgets/fixed_support_source_slab.py': 'f8a0073ff44d3e72456f92869f106647729bd098240d44d8bb72b771c5a0f99d',
    'certificates/source_norms/source-budgets/fixed_support_source_slab.json': '2d759db1497bc09d0ba3031d55fdfd42dc9f2fac27e2406dcaa60f90e7c256fc',
    'profile-notes/065-128/125-the-complete-off-face-omitted-tails-recover-every-face-constant.md': '5faf1c5ff5edf0881951c9337a431805e70edcbb8d81a8dce76cbc42d230f5b9',
    'profile-notes/129-192/134-one-complete-cost-is-uniform-on-a-nonzero-k-neighborhood.md': '156ca174c75e7ed974a164d536a10212d25928f4b20d2cfb5158ea81e4e5bdca',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable complete input')
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


def category_check():
    """Independent finite check of the general ordered-pair LCM partition."""
    labels = tuple(product(range(5), repeat=3))
    counts = Counter()
    pure = Counter()
    for first, second in product(labels, repeat=2):
        a, b, e = tuple(max(x, y) for x, y in zip(first, second))
        counts[a, b, e] += 1
        if a == e == 0 and b > 0:
            pure[b] += 1
            require(first[0] == first[2] == second[0] == second[2] == 0,
                    'No mixed-three or positive-seven pair enters the replaced category')
            require(first[1] > 0 or second[1] > 0, 'The unit square is excluded')
    require(all(n == (2*a+1)*(2*b+1)*(2*e+1) for (a, b, e), n in counts.items()),
            'Independent ordered coordinates give the original LCM multiplicities')
    require(pure == {b: 2*b+1 for b in range(1, 5)}, 'Exactly Y squared plus two unit cross terms')
    return {'maximum_coordinate': 4, 'ordered_pairs': len(labels)**2,
            'pure_five_multiplicities': dict(pure), 'unit_square_count': counts[0, 0, 0]}


def weighted_error(factorial, error, envelope):
    """Exact complete sum of (2b+1) min(error,envelope*5^-b), b>=2."""
    require(error >= 0 and envelope >= 0, 'Nonnegative shared-measure error')
    if error == 0 or envelope == 0:
        return F(0)
    cut = 2
    while envelope/F(5**cut) > error:
        cut += 1
    require(envelope/F(5**cut) <= error
            and (cut == 2 or envelope/F(5**(cut-1)) > error), 'Exact weighted infinite-tail crossing')
    return (cut*cut-4)*error+envelope*factorial.geometric(5, cut, 2, 1)


def shared_error_maximum(factorial, rho, offset, envelope, inside, outside):
    """One residual simplex, grouped by E3+omega, including all tail breakpoints."""
    knots, n, omitted_slope = {F(0), rho}, 2, None
    while envelope/F(5**n) > offset:
        x = envelope/F(5**n)-offset
        if 0 <= x <= rho:
            knots.add(x)
        # At zero source offset, infinitely many knots approach zero. Below
        # this knot the complete objective is increasing, so none can win.
        if offset == 0 and x <= rho and n*n-4 >= 3*(outside-inside):
            omitted_slope = n*n-4+3*(inside-outside)
            require(omitted_slope >= 0, 'All omitted near-zero segments increase toward a retained knot')
            break
        n += 1
        if rho == offset == 0:
            break
    values = [{'mass_in_E3_or_omega': x,
               'upper': 3*inside*x+3*outside*(rho-x)+weighted_error(factorial, offset+x, envelope)}
              for x in sorted(knots)]
    return {'inside_price': inside, 'outside_price': outside, 'source_offset': offset,
            'envelope': envelope, 'knots': values, 'omitted_near_zero_slope_lower': omitted_slope,
            'upper': max(r['upper'] for r in values)}


def joint_transport(par, shallow, factorial):
    """Actual source exclusions and one common projected error measure."""
    delta, rho = par['delta'], par['rho']
    require(0 <= delta <= F(1, 27) and 0 <= rho <= F(1, 1000)
            and 0 <= par['rbar'] <= F(1, 520) and par['gap'] > 0,
            'The complete160 source and residual domain with its forcing guards')
    c5, amin = F(2, 5)+13*delta/90, (4-delta)/5
    density = (F(0), c5-amin*(F(1, 3)-delta/18),
               c5-amin*(F(1, 9)-delta/18), c5, c5)
    hbar = F(1, 2)+delta/18
    envelope = hbar-min(density[1:])
    require(c5 == par['c'][1] and all(0 < c <= hbar for c in density[1:]),
            'Positive slot reference after the exact A/root1 and B/cell exclusions')
    rows = []
    for first_beta, first in product((2, 3, 4), range(5)):
        label = shallow.one_label_bound((5, None, first), first_beta, par)
        source = (label['finite_transport']['finite_upper']-label['reference']
                  +label['source_delta_price']*delta)
        prices = label['coordinate_prices']
        inside = max(prices[i] for i in (2, 3, 6))
        outside = max(*(prices[i] for i in (0, 1, 4, 5)), label['q_sum_price']/par['gap'])
        if first == 0:
            source = inside = outside = F(0)
        deep_rows = [(11 if chosen == first else 7)*c/40 for chosen, c in enumerate(density)]
        deep = max(deep_rows)
        shared = shared_error_maximum(factorial, rho, delta/240, envelope, inside, outside)
        upper = 3*source+deep+shared['upper']
        rows.append({'first_beta': first_beta, 'first_slot': first,
                     'first_indicator_source_upper': source, 'indicator_coordinate_prices': prices,
                     'indicator_q_sum_price': label['q_sum_price'], 'deep_Bellman_candidates': deep_rows,
                     'deep_Bellman_upper': deep, 'shared_residual_error': shared, 'upper': upper})
    result = max(r['upper'] for r in rows)
    if delta == rho == 0:
        require(result == F(49, 180), 'The transported joint bound recovers the sharp face value')
    return {'density_caps': density, 'raw_density_cap': hbar, 'common_error_envelope': envelope,
            'first_slot_rows': rows, 'joint_upper': result,
            'maximizers': [(r['first_beta'], r['first_slot']) for r in rows if r['upper'] == result]}


def complete_shell_transport(base, previous_face, shells, slab, shallow, factorial):
    """Consume each new joint block on its own already certified complete shell."""
    slab_module = module('pure_five_slab_consumer', base/'frontier/source-budgets/fixed_support_source_slab.py')
    inner = slab_module.complete_inner_comparison(base, slab)
    require(inner == slab['complete_inner_comparison'], 'Exact162 inner complete consumer reconstructed')
    square_weight = F(previous_face['complete_square_weight'])
    cE = 1-F(1, 614922)
    outputs = []
    for shell in shells['shells']:
        par = {k: tuple(map(F, v)) if isinstance(v, list) else F(v) for k, v in shell['parameters'].items()}
        old = inner if par['rho'] == F(1, 20000) else shell['comparison']
        require(par['rho'] in (F(1, 20000), F(1, 1000)), 'Exactly both complete160 shells')
        old_square = shell['square']
        old_pure = (next(F(r['weighted_upper']) for r in old_square['bounded_cylinders'] if r['modulus'] == 5)
                    +next(F(r['upper']) for r in old_square['complete_weighted_tails'] if r['family'] == 'pure5'))
        joint = joint_transport(par, shallow, factorial)
        new_pure = min(old_pure, joint['joint_upper'])
        saving = old_pure-new_pure
        require(saving > 0, 'A strictly stronger actual off-face joint block on this entire shell')
        lower = F(shell['comparison']['residual_lower'])
        N, d, M, C0 = (F(old[k]) for k in ('signed_endpoint', 'denominator_at_mass_floor', 'mass_coefficient', 'offset'))
        old_target = C0+(N+M*lower)/(d+cE*lower)
        new_N = N-square_weight*saving
        target = C0+(new_N+M*lower)/(d+cE*lower)
        remaining = (target-C0)*cE-M
        require(old_target == F(old['comparison_upper']) and d > 0 and new_N > 0
                and remaining > 0 and (target-C0)*d-new_N+remaining*lower == 0,
                'Same actual S, same complete denominator and same residual lower endpoint')
        require(old['all_original_indices'] == list(range(52)) and target < old_target,
                'All52 original independent tests remain exactly once')
        groups = {k: F(v) for k, v in old['cost_groups'].items()}
        require(groups['square_at_mass_floor'] == square_weight*(F(53, 360)
                +F(old_square['full_square_upper'])-F(old_square['mass_upper'])), 'One original actual-S square unit term')
        groups['square_at_mass_floor'] -= square_weight*saving
        outputs.append({'parameters': par, 'residual_lower': lower, 'joint_transport': joint,
                        'previous_pure_five_block': old_pure, 'new_pure_five_block': new_pure,
                        'complete_square_saving': saving,
                        'previous_square_upper': F(old_square['full_square_upper']),
                        'complete_square_upper': F(old_square['full_square_upper'])-saving,
                        'cost_groups': groups, 'signed_endpoint': new_N,
                        'denominator_at_mass_floor': d, 'mass_coefficient': M, 'offset': C0,
                        'remaining_S_coefficient': remaining, 'all_original_indices': old['all_original_indices'],
                        'comparison_upper': target, 'previous_comparison_upper': old_target,
                        'comparison_improvement': old_target-target})
    require(len(outputs) == 2 and outputs[0]['residual_lower'] == 0
            and outputs[1]['residual_lower'] == outputs[0]['parameters']['rho'], 'Two closed shells cover the whole original domain')
    return {'shells': outputs, 'uniform_comparison_upper': max(r['comparison_upper'] for r in outputs),
            'scope': 'Both original160 residual shells, with162 stronger inner heavy margins. Source radius1/27, residual radius1/1000, actual r<=1/520, both orientations. Only the complete pure-five square block changes; all52 independent costs, five denominator objectives and infinite tails remain.'}


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('pure_five_face_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    previous = read('certificates/source_norms/moments-survival/whole_quadratic_same_head.json')
    joint = read('certificates/source_norms/moments-survival/pure_five_joint_moments.json')
    shells = read('certificates/source_norms/comparison-bounds/residual_shell_k_comparison.json')
    slab = read('certificates/source_norms/source-budgets/fixed_support_source_slab.json')
    names = ('uniform_square_and_raw81_neighborhood', 'uniform_k_neighborhood_cost',
             'uniform_ap_survival_denominator', 'complete_off_face_factorial_tail',
             'complete_off_face_omitted_tails', 'vector_face_complete_ratio',
             'endpoint_numerator_common_costs', 'uniform_shallow_indicator_transport')
    modules = {n: module('pure_five_face_'+n, io.named_artifact(base/'frontier', n+'.py')) for n in names}
    closures = [r['source_sha256'] for r in (previous, joint, shells, slab)]
    closures += [getattr(m, 'PINS', {}) for m in modules.values()]
    for closure in closures:
        for path, pin in closure.items():
            require(path not in used or used[path] == pin, 'Consistent inherited source '+path)
            used[path] = pin
    for path, pin in used.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned complete input '+path)
    D, L, Qold = map(F, (previous['mass'], previous['linear_upper'], previous['complete_square_upper']))
    require((D, L, Qold) == (F(53, 360), F(1151, 1800), F(374, 75))
            and previous['r'] == previous['rho'] == '0', 'The same whole saturated actual faces')
    par = modules['uniform_k_neighborhood_cost'].parameters(F(0), F(0))
    square = modules['uniform_square_and_raw81_neighborhood'].uniform_square(
        par, modules['uniform_ap_survival_denominator'], modules['complete_off_face_factorial_tail'],
        modules['complete_off_face_omitted_tails'])
    first = next(r['weighted_upper'] for r in square['bounded_cylinders'] if r['modulus'] == 5)
    deep = next(r['upper'] for r in square['complete_weighted_tails'] if r['family'] == 'pure5')
    old_component = first+deep
    new_component = F(joint['new_pure_five_square_with_unit_cross'])
    saving = old_component-new_component
    Q = square['full_square_upper']-saving
    require(first == F(14, 75) and deep == F(11, 100) and old_component == F(89, 300),
            'Exactly the original zero-three zero-seven pure-five block with its unit cross')
    require((new_component, saving, Q) == (F(49, 180), F(11, 450), F(2233, 450))
            and old_component == F(joint['old_pure_five_square_with_unit_cross'])
            and Q == F(joint['full_face_square_upper']) and square['full_square_upper'] == Qold,
            'The sharp joint block is substituted exactly once into the same original square')
    new_zero7 = square['zero7_pair_upper']-saving
    require(new_zero7 == F(4607, 1800)
            and square['raw35_pair_upper']*square['positive7_factor'] == F(173, 72)
            and new_zero7+F(173, 72) == Q, 'All positive-seven and other zero-seven pair classes remain')
    engine = module('pure_five_face_inventory', base/'frontier/source-budgets/source_barrier_saturation.py').Experiment(base)
    require(all(path in used and used[path] == pin for path, pin in engine.pins.items()), 'The whole original52-cost inventory is pinned')
    tags = [s['tag'] for s in engine.specs+engine.quadratic_specs]+[('s', F(81, n*n)) for n in range(1, 7)]
    require(len(tags) == 52, 'All41 linear, five transformed quadratic and six raw81 tags')
    all_tags = [('h', F(0)), ('s', F(0))]+tags
    functions = [lambda v, tag=t: engine.source.zero5_cost(tag, v) for t in all_tags]
    metadata = [engine.source.zero5_cost_metadata(t) for t in all_tags]
    old_costs = list(map(F, previous['improved_cost_bounds']))
    weights = list(map(F, previous['cost_weights']))
    costs, proofs = modules['vector_face_complete_ratio'].propagate(
        modules['endpoint_numerator_common_costs'], functions, metadata, old_costs, old_costs, D, L, Q)
    signed, square_weight = F(previous['signed_mass_coefficient']), F(previous['complete_square_weight'])
    require(len(costs) == len(weights) == 52 and min(weights) > 0 and signed < 0 < square_weight,
            'Every original positive cost and both signed complement terms retained')
    old_N = signed*D+sum(w*c for w, c in zip(weights, old_costs))+square_weight*Qold
    N = signed*D+sum(w*c for w, c in zip(weights, costs))+square_weight*Q
    propagated_gain = sum(w*(a-b) for w, a, b in zip(weights, old_costs, costs))
    direct_gain = square_weight*saving
    require(old_N == F(previous['numerator_upper']) and old_N-N == direct_gain+propagated_gain
            and direct_gain > 0 and propagated_gain >= 0 and N > 0, 'Every complete numerator gain counted exactly once')
    denominator = D-F(previous['standalone_hinge4_penalty'])-(
        sum(F(r['joint_mean_upper']) for r in previous['AP11_block_results'])
        +F(previous['full_count_tail']['remaining_cost_upper']))/7
    require(denominator == F(previous['uniform_denominator_lower']) == F(50511415637, 632754738000) > 0,
            'All four complete AP11 blocks, full count remainder and independent AP13 loss retained')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    require(offset+old_N/denominator == F(previous['comparison_upper'])
            and 403 < comparison < F(previous['comparison_upper']), 'Strict complete-face gain, still above403')
    shallow, factorial = modules['uniform_shallow_indicator_transport'], modules['complete_off_face_factorial_tail']
    zero_transport = joint_transport(par, shallow, factorial)
    shell_transport = complete_shell_transport(base, previous, shells, slab, shallow, factorial)
    return {'schema': 'erdos7-pure-five-complete-face-comparison-v1', 'source_sha256': used,
            'faces': previous['faces'], 'r': F(0), 'rho': F(0), 'mass': D, 'linear_upper': L,
            'LCM_category_check': category_check(), 'original_square_categories': square,
            'old_pure_five_block': old_component, 'new_pure_five_block': new_component,
            'complete_square_saving': saving, 'new_zero7_pair_upper': new_zero7,
            'previous_square_upper': Qold, 'complete_square_upper': Q,
            'original_cost_tags': tags, 'cost_weights': weights, 'previous_cost_bounds': old_costs,
            'majorants': proofs, 'improved_cost_bounds': costs,
            'improved_cost_indices': [i for i, (a, b) in enumerate(zip(old_costs, costs)) if b < a],
            'signed_mass_coefficient': signed, 'complete_square_weight': square_weight,
            'direct_numerator_gain': direct_gain, 'propagated_numerator_gain': propagated_gain,
            'previous_numerator': old_N, 'numerator_upper': N,
            'AP11_block_results': previous['AP11_block_results'], 'full_count_tail': previous['full_count_tail'],
            'standalone_hinge4_penalty': F(previous['standalone_hinge4_penalty']),
            'uniform_denominator_lower': denominator, 'offset': offset,
            'previous_comparison': F(previous['comparison_upper']), 'comparison_upper': comparison,
            'comparison_improvement': F(previous['comparison_upper'])-comparison,
            'face_transport_check': zero_transport, 'complete_neighborhood_transport': shell_transport,
            'scope': 'Ordinary complete comparison on both whole actual saturated K faces and complete160 source neighborhood. The pure-five joint moment replaces exactly one full LCM block, including its unit cross terms; all52 costs, full polynomial and geometric tails, other square categories and the full survival denominator remain. Off-face slot references and the first indicator share one actual residual budget. No new global K, Lean verification or unrestricted Erdos7 conclusion.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('pure_five_face_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete-face joint-moment certificate')
    print('PASS: complete face comparison='+str(float(F(result['comparison_upper'])))+
          '; gain='+str(float(F(result['comparison_improvement'])))+
          '; propagated rows='+str(result['improved_cost_indices']))
    print('PASS: complete neighborhood comparison='+str(float(F(
        result['complete_neighborhood_transport']['uniform_comparison_upper']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
