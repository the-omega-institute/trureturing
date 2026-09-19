#!/usr/bin/env python3
"""Complete effective9 source comparison with total alpha at most 1/20."""
import argparse
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/ineffective15_complete_source_comparison.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'certificates/source_norms/allocated_seven_thresholds.json': '9400e4fae0a400edcc7ee7459103af677e512592823b683f67e7c896f8d345b8',
    'frontier/verify_allocated_seven_thresholds.py': 'c9490ee0f1b5943d6b9f37d5fb1b29c8db4cffe5fce77b052dffbf70368985d2',
    'profile-notes/49-full-linear-and-quadratic-carriers-refine-the-frontier.md': 'fb65fb2a313b8cc937a0f1c5ac0314c1fc1cda55c045e27ffe1c2a70d107c931',
    'profile-notes/53-allocated-seven-thresholds-sharpen-actual-survival.md': 'e046b8ad8291b0b94963ce33a7ce10bf11710b972a872f8d7d8801c04fdab928',
    'profile-notes/35-ap45-layout-costs-and-complete-core-tails.md': '69b81701e966910e69552f20f255f6a36bf345ea49cb684a46dd11f0148e3a26',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: '+key)
        result[key] = value
    return result


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable existing source '+str(path))
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


def digest(value, sort_keys=False):
    return sha256(json.dumps(encode(value), sort_keys=sort_keys, separators=(',', ':')).encode()).hexdigest()


def reconstruct(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical certificate reader')
    io = module('ineffective15_io', base/'certificate_io.py')
    pins = dict(PINS)
    old53 = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/allocated_seven_thresholds.json'),
                       object_pairs_hook=unique)
    require(old53['schema'] == 'erdos7-allocated-seven-thresholds-v1'
            and old53['verifier_sha256'] == PINS['frontier/verify_allocated_seven_thresholds.py'],
            'Published original53 source and verifier')
    for entries in (old53['source_sha256'], old53['helper_sha256']):
        for path, pin in entries.items():
            require(path not in pins or pins[path] == pin, 'Consistent original source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned original source '+path)

    def read(path):
        require(path in pins, 'Certificate is in the original source closure '+path)
        return json.loads(io.read_artifact_bytes(base/path), object_pairs_hook=unique)

    def load(path):
        require(path in pins, 'Module is in the original source closure '+path)
        return module('ineffective15_'+Path(path).stem, base/path)

    source = load('verify_joint_frontier.py')
    fixed = load('frontier/fixed_cost.py')
    layout = load('frontier/layout_gap.py')
    ap = load('frontier/ap_schedule.py')
    profiles = load('frontier/shared_source_deficits.py')
    linear = load('frontier/shared_linear_refinement.py')
    square = load('frontier/shared_square_barrier.py')
    allocated = load('frontier/allocated_seven_thresholds.py')
    old39, old46, old47, old49 = (read('certificates/source_norms/'+name+'.json') for name in (
        'shared_source_deficits', 'joint_survival_carriers', 'joint_linear_carriers', 'full_linear_carrier_frontier'))
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    quadratic = read('certificates/source_norms/retained_quadratic_tests.json')
    quadratic_inputs = read('certificates/source_norms/retained_quadratic_inputs.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    rows, source_stats = profiles.aggregate(source, fixed, layout, ap, parent, quadratic,
                                            quadratic_inputs, ap_inputs)
    rows, linear_stats = linear.refine(source, fixed, ap, ap_inputs, rows)
    rows, square_stats = square.refine(source, fixed, rows, source_stats['quadratic_tail_weight'])
    require(encode(source_stats) == old39['source_profiles']
            and encode(linear_stats) == old39['linear_refinement']
            and encode(square_stats) == old39['square_barrier_refinement'],
            'Reconstruct the complete original39 source and every refinement')
    original_row_hash = digest(rows, sort_keys=True)
    require(original_row_hash == old39['source_profile_sha256']
            == old49['predecessor_source_profile_sha256'] == old53['predecessor_source_profile_sha256'],
            'All original39 source values match the complete published digest')
    rows, stats = allocated.reconstruct(source, old46, rows)
    require(encode(stats) == old53['allocation_statistics'], 'All original53 allocated margins and tails')
    return dict(io=io, pins=pins, source=source, allocated=allocated, rows=rows,
                old47=old47, old49=old49, old53=old53, load=load, read=read,
                original_row_hash=original_row_hash, allocation_statistics=stats)


def original_endpoints(data):
    source, allocated = data['source'], data['allocated']
    old47, old49, old53 = data['old47'], data['old49'], data['old53']
    q, reference, offset = allocated.Q, F(old53['combined']), source.WHOLE_CONST
    H16, H41, A81, cG = (F(old49[k]) for k in ('H16', 'H41', 'A81', 'cG'))
    slope = source.AC*H16+H41+A81
    mass_coefficient = q*(reference-offset)-slope
    require(q == F(23, 42) and mass_coefficient > 0, 'Original full K target and signed coefficient')
    oldlinear = [r for a in old47['six_linear']['row_blocks'] for b in a for r in b]
    refined = {r['index']: r for block in old49['frontier']['row_blocks'] for r in block}
    vertices = list(source.vertices())
    finite, tails = source.ap_product_distribution(allocated.CAPS, 9)
    require(cG == tails[2]+sum(v*v*finite[v] for v in (7, 8)), 'Entire original raw81 square coefficient')
    endpoints, component_rows, original_endpoints = {}, [], []
    for row in data['rows']:
        i, raw = row['index'], row['s']
        dat = source.data(vertices[i])
        raw81 = sum(prob*v*v*source.square357(F(81, v*v), dat)
                    for v, prob in finite.items() if v < 7)
        for j, cond in enumerate(row['conditional']):
            require(tuple(cond['carrier']) == allocated.CARRIERS[j], 'Original common carrier order')
            low, M = cond['D_c'], cond['M']
            Qfull = F(refined[i]['conditional_Mquad'][j]) if i in refined else row['Mquad']
            Gfull = F((refined[i] if i in refined else oldlinear[i])['conditional_M41'][j])
            mg = row['source_margin']
            correction = source.AC*Qfull+Gfull+cG*mg-raw81
            gap_low = mass_coefficient*low+(reference-offset)*M+correction
            gap = mass_coefficient*raw+(reference-offset)*M+correction
            payment = q*raw+M
            require(gap == gap_low+mass_coefficient*(raw-low)
                    and 0 < q*low+M <= low <= raw and 0 < payment <= raw,
                    'Both original denominator payments and exact common upper-mass gap')
            endpoints[i, j] = ((gap_low, q*low+M), (gap, payment))
            component_rows.append((i, j, raw, low, M, Qfull, Gfull, mg, raw81, correction, gap, payment))
            original_endpoints.extend(((i, j, 'D_c', gap_low), (i, j, 's', gap)))
    require(len(endpoints) == 23328 and len(vertices) == 1296 and len(refined) == 24,
            'All original source/carrier pairs, refined vertices and signed correction components')
    return dict(vertices=vertices, q=q, reference=reference, offset=offset,
                numerator_slope=slope, mass_coefficient=mass_coefficient, endpoints=endpoints,
                component_rows=component_rows, original_endpoints=original_endpoints,
                correction_coefficients={'AC': source.AC, 'cG': cG, 'H16': H16, 'H41': H41, 'A81': A81})


def calculate(base):
    data = reconstruct(base)
    original = original_endpoints(data)
    old53 = data['old53']
    vertices, q, reference, offset, slope, mass_coefficient = (original[k] for k in
        ('vertices', 'q', 'reference', 'offset', 'numerator_slope', 'mass_coefficient'))
    vertex_index = {v: i for i, v in enumerate(vertices)}
    endpoints = {key: pair[1] for key, pair in original['endpoints'].items()}
    floors, controllers, counts, floor_rows = {}, {}, Counter(), []
    signed403 = q*(403-offset)-slope
    require(signed403 < 0 and 403 > offset, 'Use actual upper mass for the negative target403 coefficient')
    for (i, j), (gap, payment) in endpoints.items():
        value = gap-(reference-403)*payment
        alpha = next((k+1 for k, v in enumerate(vertices[i][1]) if v), 0)
        z = int(vertices[i][4] == 1)
        key = alpha, z
        counts[key] += 1
        floor_rows.append((i, j, value))
        if key not in floors or value < floors[key]:
            floors[key], controllers[key] = value, [(i, j)]
        elif value == floors[key]:
            controllers[key].append((i, j))
    require(len(floors) == 6 and set(counts.values()) == {3888},
            'Every complete original source/carrier pair appears in exactly one of six floors')
    require(all(floors[k, 1] > 0 for k in range(3)) and floors[0, 0] > 0
            and floors[1, 0] < 0 and floors[2, 0] < 0, 'Exact six-floor signs')

    def interpolate(t, a0, a1):
        return ((1-t)*((1-a0-a1)*floors[0, 1]+a0*floors[1, 1]+a1*floors[2, 1])
                +t*((1-a0-a1)*floors[0, 0]+a0*floors[1, 0]+a1*floors[2, 0]))

    tstar = min(floors[k, 1]/(floors[k, 1]-floors[k, 0]) for k in (1, 2))
    astar = min(floors[0, 0]/(floors[0, 0]-floors[k, 0]) for k in (1, 2))
    zstar, alphastar = 1-tstar/4, astar/4
    require(0 < tstar < 1 and 0 < astar < 1
            and all(interpolate(t, a0, a1) >= 0 for t in (0, tstar)
                    for a0, a1 in ((0, 0), (1, 0), (0, 1)))
            and all(interpolate(t, a0, a1) >= 0 for t in (0, 1)
                    for a0, a1 in ((0, 0), (astar, 0), (0, astar))),
            'Complete high-z and low-total-alpha rectangles follow from multi-affine endpoints')
    ceil = lambda x: -(-x.numerator//x.denominator)
    zr = F(ceil(1000*zstar), 1000)
    scaled_alpha = 1000*alphastar
    ar = F(scaled_alpha.numerator//scaled_alpha.denominator, 1000)
    require(zstar <= zr <= 1 and 0 < ar <= alphastar
            and all(interpolate(4*(1-zr), a0, a1) >= 0 for a0, a1 in ((0, 0), (1, 0), (0, 1)))
            and all(interpolate(t, a0, a1) >= 0 for t in (0, 1)
                    for a0, a1 in ((0, 0), (4*ar, 0), (0, 4*ar))), 'Exact rational subset rectangles')

    mix = F(1, 5)
    records = []
    for (i, j), (gap, payment) in endpoints.items():
        v = vertices[i]
        zero = (v[0], (F(0), F(0)), v[2], v[3], v[4])
        zero_i = vertex_index[zero]
        gap0, payment0 = endpoints[zero_i, j]
        gm, em = (1-mix)*gap0+mix*gap, (1-mix)*payment0+mix*payment
        require(em > 0, 'Positive mixed original denominator payment')
        records.append({'vertex': i, 'zero_alpha_vertex': zero_i, 'carrier_index': j,
                        'mixed_signed_gap': gm, 'mixed_denominator_payment': em,
                        'required_target': reference-gm/em})
    target = max(r['required_target'] for r in records)
    final_slope = q*(target-offset)-slope
    require(offset < target < 403 and final_slope < 0,
            'Final full-source target satisfies all interpolation signs and strictly crosses403')
    mixed_controls, slacks = [], []
    for r in records:
        slack = r['mixed_signed_gap']-(reference-target)*r['mixed_denominator_payment']
        require(slack >= 0, 'Every exact original mixed target inequality')
        slacks.append(slack)
        if slack == 0:
            mixed_controls.append((r['vertex'], r['carrier_index']))
    six_margin = min((1-mix)*floors[0, z]+mix*floors[k, z] for k in range(3) for z in range(2))
    require(six_margin > 0 and len(records) == 23328 and F(1, 4)*mix == F(1, 20),
            'The complete smaller alpha simplex has a separate strictly positive target403 floor')

    # Original terminal errors apply to full and retained families. Only the
    # missing/ineffective15 sufficient branch is claimed stable under retention.
    core = data['load']('frontier/ap_schedule_core.py')
    kc = data['load']('verify_killed_core_continuity.py')
    pure = data['read']('certificates/pure_root_profile_certificate.json')
    core_inputs, core_rows = core.core_errors(kc, pure['source_inputs'], F(old53['Gamma13']),
                                            F(old53['rho']), F(old53['T13_81']), F(old53['bound']))
    require(encode(core_inputs) == old53['source_inputs'] and len(core_rows) == 2,
            'The original common actual357/AP13 source constants and two complete core interfaces')
    root3, root5 = F(1, 3)-F(1, 6), F(1, 5)-F(1, 20)
    require(root3 > 0 and root5 > 0 and root3*root5 == F(1, 40),
            'Exact pure-root slack proves ineffective15 requires a retained first-level blocker')
    core_results = []
    for i, (row, old) in enumerate(zip(core_rows, old53['core_errors'])):
        require(all(encode(v) == old[k] for k, v in row.items()), 'Every original complete core error term')
        box = dict(row['box'])
        require(box[3] >= 2 and box[5] >= 1, 'Both cores retain the original3,5,9 and15 labels when present')
        margin = 403-target-row['total']
        require(margin > 0, 'The stable missing/ineffective15 branch clears the entire original core error')
        core_results.append({'box': row['box'], 'current': row['current'],
                             'original_source_inputs': core_inputs,
                             'mask_error': row['mask'], 'incoming_error': row['incoming'],
                             'whole_test_tail_error': row['test'], 'complete_error': row['total'],
                             'source_comparison_upper': target, 'comparison_plus_error': target+row['total'],
                             'strict403_margin': margin, 'test_labels': row['test_labels'],
                             'forbidden_label_count_upper': row['forbidden_label_count_upper'],
                             'preserved_branch': 'Original effective9 with absent15 or15 disjoint from the pure3 times pure5 survivor.',
                             'conclusion': 'Strict negative-Q sufficient criterion for this retained-family branch; no later-prime continuation.'})
    for path, pin in data['pins'].items():
        require(sha256(data['io'].read_artifact_bytes(base/path)).hexdigest() == pin, 'Stable final original input '+path)
    result = {
        'schema': 'erdos7-ineffective15-complete-source-comparison-v1', 'source_sha256': data['pins'],
        'original_source_profile_sha256': data['original_row_hash'],
        'allocation_statistics': data['allocation_statistics'],
        'original_reference_target': reference, 'original_offset': offset, 'survival_mass_coefficient': q,
        'numerator_slope': slope, 'original_signed_mass_coefficient': mass_coefficient,
        'correction_formula': 'AC*Q_full+G_full+cG*m_g-R81',
        'correction_coefficients': original['correction_coefficients'],
        'complete_source_pairs': len(endpoints), 'all_original_correction_rows_sha256': digest(original['component_rows']),
        'all_original_endpoint_rows_sha256': digest(original['original_endpoints']),
        'target403_signed_mass_coefficient': signed403,
        'six_floor403': {'target': 403, 'pairs_per_floor': 3888,
                        'floors': [{'alpha_vertex': k, 'z_vertex': z, 'floor': floors[k, z],
                                    'controllers': controllers[k, z]} for k in range(3) for z in range(2)],
                        'upper_mass_endpoint_sha256': digest(floor_rows),
                        'high_z_minimum': zstar, 'low_total_alpha_maximum': alphastar,
                        'high_z_rational_subset': zr, 'low_total_alpha_rational_subset': ar},
        'alpha_total_cap': F(1, 20), 'occupied_alpha_vertex_weight': mix,
        'complete_source_upper': target, 'signed_mass_coefficient_at_upper': final_slope,
        'strict403_source_gap': 403-target, 'six_floor403_margin': six_margin,
        'minimum_fixed_target_margin': min(slacks), 'controllers': mixed_controls,
        'full_mixed_endpoint_sha256': digest(records, sort_keys=True),
        'branch_preservation': {'retained_required_labels': [3, 5, 9],
                                'unblocked_mod3_root_mass_lower': root3,
                                'unblocked_mod5_root_mass_lower': root5,
                                'unblocked15_product_mass_lower': root3*root5,
                                'scope': 'Absent or ineffective15 is stable; an arbitrary numerical alpha_total<=1/20 condition is not asserted stable.'},
        'core_comparisons': core_results,
        'scope': 'Ordinary complete effective9 source inequality on the whole actual alpha_total<=1/20 domain, with all other original parameters, independent tests, carriers and exponent tails. The two complete terminal-error conclusions apply only to the preserved absent/ineffective15 branch. The six target403 floors separately certify their stated source regions. No all-source403 theorem, actual attainment, later-prime continuation, Lean verification or unrestricted Erdos7 resolution.'}
    return encode(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('ineffective15_writer_io', args.base/'certificate_io.py')
    if args.write or args.output is not None:
        io.write_certificate_text(args.output if args.output is not None else args.base/CERTIFICATE,
                                  json.dumps(result, indent=2)+'\n')
    else:
        stored = json.loads(io.read_artifact_bytes(args.base/CERTIFICATE), object_pairs_hook=unique)
        require(result == stored, 'Every complete source comparison and terminal error recomputes exactly')
    print('PASS complete effective9 alpha_total<=1/20 source upper '+str(float(F(result['complete_source_upper']))))
    print('PASS23328 original source/carrier pairs, six403 floors, two preserved absent/ineffective15 core branches')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        raise SystemExit(1)
