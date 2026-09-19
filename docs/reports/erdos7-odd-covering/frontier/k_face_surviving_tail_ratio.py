#!/usr/bin/env python3
"""Peel surviving old tails before the seven bridge on both complete K faces.

The fourth selected increment at threshold4 is identically affine. Thus
the stronger surviving tail caps change each old layout cost by the same
constant. The pinned250000-layout result is reused, not re-enumerated.
The complete comparison retains the entire preceding numerator.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/k_face_surviving_tail_ratio.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/endpoint_k_face_forced27.py': '8e5b5267397b8ca4d9cf0477b9c9074ae9e38e8171f1e4eb05a47595ad1df961',
    'certificates/source_norms/endpoint_k_face_forced27.json': '8f4c5fe37ed46d45c914f21872b2e4d00a2091adf028a0497cdd1817f82f8da0',
    'frontier/k_face_common_seven_hinges.py': '8cc4600c9b3f2f65a11820fcb2d0d6663c765c20765bbaf1ae0de6e883cefc97',
    'certificates/source_norms/k_face_common_seven_hinges.json': '002f286cce356e477f11e98fdd7bdb9d834f0c707691eee156eb17a77f03686d',
    'frontier/k_face_complete_ratio.py': 'd856e5c2face117c993b7bd308903a3fb149293d254046f76b6ff5f42ec9b478',
    'certificates/source_norms/k_face_complete_ratio.json': '7041b3c1b2d61e2063c2c97f89daccbd65b75b444a296bbc8badf4b8ffa8e426',
}
FACES = (((398, 410, 422), (1, 1)), ((616, 628, 640), (1, 0)))
LAYOUT_DIGEST = '284eded39badbe55b2f93c39e9bd3a3dc16f62fd476f3af089340cd34894be16'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module')
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


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('surviving_tail_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    geometry = read('certificates/source_norms/endpoint_k_face_forced27.json')
    hinges = read('certificates/source_norms/k_face_common_seven_hinges.json')
    previous = read('certificates/source_norms/k_face_complete_ratio.json')
    for record in (geometry, hinges, previous):
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited dependency')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    faces = [{'vertices': list(indices), 'carrier': list(carrier)} for indices, carrier in FACES]
    require(previous['faces'] == faces, 'Same two complete comparison faces')
    for record in (geometry, hinges):
        require(record['face_vertices'] == faces[0]['vertices'] and record['carrier'] == faces[0]['carrier']
                and record['symmetric_face_vertices'] == faces[1]['vertices']
                and record['symmetric_carrier'] == faces[1]['carrier'], 'Same actual surviving measures')
    D, L = F(previous['mass']), F(previous['linear_upper'])
    require((D, L) == (F(53, 360), F(1151, 1800))
            and F(geometry['surviving_mass']) == F(hinges['surviving_mass']) == D
            and F(geometry['linear_upper']) == L, 'Retain mass and complete first moment')

    # Sum all old labels outside the six-label head, on the actual survivor.
    cats = geometry['complete_nonunit_zero7_categories']
    names = ('pure3_deep', 'pure5_deep', '3_times_deep5', '9_times_deep5', 'deep35')
    tail_categories = {name: F(cats[name]) for name in names}
    require(list(tail_categories.values()) == [F(7, 180), F(1, 50), F(1, 75), F(1, 225), F(1, 72)],
            'All complete surviving tail categories')
    total = sum(tail_categories.values())
    c5, c15, c45 = map(F, geometry['complete_descendant5_coefficients'])
    c3 = F(cats['pure3_deep'])/(F(1, 27)/(1-F(1, 3)))
    require((c3, c5, c15, c45, total) == (F(7, 10), F(2, 5), F(4, 15), F(4, 45), F(163, 1800)),
            'Complete geometric sums with the actual surviving coefficients')
    selected_caps = {25: c5/25, 27: c3/27, 75: c15/25, 81: c3/81}
    selected = {4: (25, 27, 75), 5: (25, 27, 75, 81)}
    remainder = {t: total-sum(selected_caps[n] for n in labels) for t, labels in selected.items()}
    require(remainder == {4: F(41, 1080), 5: F(19, 648)}, 'Full surviving remainders after exact label removal')

    # The old fourth81 increment is w at threshold4, independent of layout.
    bridge = module('surviving_tail_bridge', base/'frontier/k_face_common_seven_hinges.py')
    require(tuple(bridge.ORDER) == ((0, 2), (3, 0), (1, 2), (4, 0)), 'The actual selected order25,27,75,81')
    pre, raw, w, _ = bridge.source_tables(2)
    require(encode(raw) == hinges['source_upper_table'] and encode(w) == hinges['retained_density'],
            'Same raw bridge and selected-deletion upper density')
    affine_checks = 0
    for weight in sorted({x for row in w for x in row}):
        for extra in range(3):
            f = lambda v: weight*max(v-4, 0)+bridge.seven_increment(4, v, extra)
            for B in range(1, 7):
                require(f(B+4)-f(B+3) == weight, 'Every possible six-label head has affine fourth increment')
                affine_checks += 1
    p81 = max(sum(pre[c][s]*w[c][s] for s in range(5)) for c in range(5))/81
    require(p81 == F(71, 8100), 'Layout-independent raw weighted81 cap')
    old_tail, seven_tail = F(hinges['remaining_old_tail']), F(hinges['remaining_positive7'])
    require((old_tail, seven_tail) == (F(2389, 81000), F(779, 12600)), 'Complete inherited complementary tails')
    shifts = {4: old_tail+p81-remainder[4], 5: old_tail-remainder[5]}
    require(shifts == {4: F(1, 3375), 5: F(7, 40500)}, 'Positive constant improvements for every layout')
    require(hinges['joint_layout_checks'] == 250000 and hinges['all_layout_and_dual_sha256'] == LAYOUT_DIGEST,
            'Reuse the exact complete layout and LP-dual certificate')
    bounds, components, gains53 = {}, {}, {}
    for t in (4, 5):
        old_bound = F(hinges['uniform_hinge_uppers'][str(t)])
        witness = hinges['maximizing_witnesses'][str(t)]
        head, tails = F(witness['source_head_lp']), F(witness['selected_old_tail'])
        require(head+tails+old_tail+seven_tail == old_bound, 'Reconstruct inherited uniform maximum')
        finite_selected = tails-(p81 if t == 4 else 0)
        bound = head+finite_selected+remainder[t]+seven_tail
        require(bound == old_bound-shifts[t] > 0, 'Identical constant subtraction on the complete layout domain')
        require(F(previous['hinge_uppers'][str(t)]) == old_bound, 'The preceding comparison uses exactly these hinges')
        gain = F(hinges['old53_face_hinge_ranges'][str(t)]['minimum_on_full_relaxed_face'])-bound
        require(gain > 0, 'Uniform improvement relative to the minimum of the old whole-face cap')
        bounds[t], gains53[t] = bound, gain
        components[t] = {'source_head_lp': head, 'selected_old_tail': finite_selected,
                         'surviving_old_remainder': remainder[t], 'positive7_remainder': seven_tail}
    require(bounds == {4: F(938213, 4630500), 5: F(1523903, 9724050)}, 'Exact new whole-face hinges')

    # Reuse every term of the already complete numerator, including its sign.
    weights = list(map(F, previous['cost_weights']))
    costs = list(map(F, previous['improved_cost_bounds']))
    residual = F(previous['signed_mass_coefficient'])
    square_weight, Q = F(previous['complete_square_weight']), F(previous['square_sums']['full_square_upper'])
    require(len(costs) == len(weights) == 52 and residual < 0 < square_weight and min(weights) > 0,
            'All signed-mass and52 positive-cost coefficients are retained')
    N = residual*D+sum(wi*ci for wi, ci in zip(weights, costs))+square_weight*Q
    require(N == F(previous['numerator_upper']) > 0 and Q == F(374, 75), 'Entire preceding numerator unchanged')
    U4, U5 = bounds[4], bounds[5]
    coefficients = {'mass': F(945008, 922383), 'linear': F(45253, 1844766),
                    'hinge4': F(346061, 1844766), 'hinge5': F(4, 33)}
    denominator = coefficients['mass']*D-coefficients['linear']*L-coefficients['hinge4']*U4-coefficients['hinge5']*U5
    p = lambda n: F(28, 33) if n == 1 else F(50, 3*11**n)
    r = F(1, 11)
    tail0, tail1 = F(50, 3)*r**5/(1-r), F(50, 3)*r**5*(5-4*r)/(1-r)**2
    require({'mass': str(tail0), 'first_moment': str(tail1)} == previous['full_AP11_tail'], 'Entire original AP11 tail')
    interpolation = lambda t: (4-t)*(L-D)/3+(t-1)*U4/3
    full = D-U4/6-(p(1)*U5+sum(p(n)*n*interpolation(F(5, n)) for n in (2, 3, 4))+tail1*L-5*tail0*D)/7
    old_denominator = F(previous['uniform_denominator_lower'])
    denominator_gain = coefficients['hinge4']*shifts[4]+coefficients['hinge5']*shifts[5]
    require(full == denominator == old_denominator+denominator_gain > old_denominator > 0,
            'Complete AP11 expansion, coefficient expansion and exact positive gain agree')
    require(denominator == F(40455251803, 517708422000), 'Exact new uniform denominator')
    offset = F(previous['offset'])
    comparison = offset+N/denominator
    old_comparison = F(previous['comparison_upper'])
    require(old_comparison == offset+N/old_denominator and 403 < comparison < old_comparison,
            'Positive denominator lowers the complete comparison but does not reach the target')
    return {'schema': 'erdos7-k-face-surviving-tail-ratio-v1', 'source_sha256': used,
            'faces': faces, 'mass': D, 'linear_upper': L,
            'complete_surviving_old_tail_categories': tail_categories, 'complete_surviving_old_tail': total,
            'selected_surviving_cylinder_caps': selected_caps, 'selected_old_tail_labels': selected,
            'surviving_old_remainders': remainder, 'affine_fourth_increment_checks': affine_checks,
            'old_weighted81_cap': p81, 'constant_improvements_over83': shifts,
            'reused_joint_layout_checks': hinges['joint_layout_checks'], 'reused_all_layout_and_dual_sha256': LAYOUT_DIGEST,
            'reused_maximizing_layouts': hinges['maximizing_layouts'], 'maximizing_bound_components': components,
            'uniform_hinge_uppers': bounds, 'uniform_improvements_over53': gains53,
            'retained_numerator': {'signed_mass_coefficient': residual, 'cost_weights': weights,
                                   'cost_upper_bounds': costs, 'complete_square_weight': square_weight,
                                   'complete_square_upper': Q, 'numerator_upper': N},
            'full_AP11_tail': {'mass': tail0, 'first_moment': tail1}, 'denominator_coefficients': coefficients,
            'uniform_denominator_gain_over84': denominator_gain, 'uniform_denominator_lower': denominator,
            'offset': offset, 'comparison_upper': comparison, 'comparison_improvement_over84': old_comparison-comparison,
            'scope': 'Ordinary proof on both complete actual K-control faces at saturated mass. Peels the whole remaining zero-seven load on the actual survivor before applying the raw seven bridge. Retains independent original residues, all tails and the entire preceding numerator. No actual attainment, sharpness, off-face neighborhood, global K update, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('surviving_tail_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact surviving-tail comparison certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: actual-survivor tails, constant layout shifts, unchanged complete numerator and AP11 tail.')
    print('Both entire K faces: denominator '+str(float(F(result['uniform_denominator_lower'])))
          +'; comparison '+str(float(F(result['comparison_upper'])))+'.')


if __name__ == '__main__':
    main()
