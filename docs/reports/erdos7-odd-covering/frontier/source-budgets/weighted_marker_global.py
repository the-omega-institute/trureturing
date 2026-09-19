#!/usr/bin/env python3
"""Weighted original5 cancellation for41 linear costs and a complete K bound.

The ordinary proof retains the weighted event before source and deletion
are combined. All chosen costs keep independent original tests. Their
penalties add against one actual mass residual; no preceding identity
improvement is added a second time.
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
CERTIFICATE = 'certificates/source_norms/source-budgets/weighted_marker_global.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/endpoint-bounds/broad_marked_identity_global.py': '02a9202d81951a0861bfdedb43127a375595028a26b1ac5002f8a0b195063998',
    'certificates/source_norms/endpoint-bounds/broad_marked_identity_global.json': '62d60d6746dba0d99f9b81c5dab2fbfa7694bfddba8bd1e19868ad7b0dded8bc',
}
CHOSEN = (4, 5, 6, 9, 11, 13, 14, 15, 20, 21, 22, 25, 27, 29, 30, 31, 34, 35, 37, 38, 39, 40)


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
    io = module('weighted_marker_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous = read('certificates/source_norms/endpoint-bounds/broad_marked_identity_global.json')
    for path, pin in previous['source_sha256'].items():
        require(path not in used or used[path] == pin, 'Consistent inherited input')
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
        used[path] = pin
    current74 = read('certificates/source_norms/source-budgets/global_k_face_gain.json')
    old49 = read('certificates/source_norms/source-budgets/full_linear_carrier_frontier.json')
    broad = read('certificates/source_norms/endpoint-bounds/broad_five_slot_tradeoff.json')
    source = module('weighted_marker_source', base/'verify_joint_frontier.py')
    schedule = module('weighted_marker_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('weighted_marker_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    specs, groups, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    require(len(specs) == 46 and len(source.BASES) == 10, 'All41 linear and five quadratic original costs')
    group_weights = {'R17': F(1), 'R19': source.P17, 'R5': source.EXTRA5}
    identity_weight = sum(group_weights[g['name']]*g['tail_coefficient'] for g in groups)
    require(identity_weight == F(previous['identity_cost_coefficient']), 'Entire complementary AP weight')

    delta, rcut = F(2, 27), F(1, 2500)
    source_weight = 1-(1+delta)/5
    eta_min, h1_min, Delta_max = F(1, 9)-delta/18, F(1, 3)-delta/6, 3*delta/4
    guards = {'pure5_slot': F(1, 10)-rcut, 'alpha_slot': h1_min/5-rcut,
              'beta_slot': eta_min/5-rcut, 'remaining_slot': h1_min*(F(1, 10)-Delta_max)-2*rcut}
    gap = min(guards.values())
    common_penalty = max(F(1), F(1, 9)/gap)
    best_slot_credit = F(1, 50)-rcut/5
    min_credit = min(source_weight*gap, best_slot_credit)
    deep_payment = F(13, 6075)
    require(delta < F(1, 2) and Delta_max == F(broad['slab']['delta_upper']) == F(1, 18)
            and rcut < min(F(1, 10), h1_min/5, eta_min/5), 'General packing hypotheses for the full concentration region')
    require((source_weight, gap, common_penalty, min_credit)
            == (F(106, 135), F(12271, 911250), F(101250, 12271), F(650363, 61509375)),
            'Exact carrier-density, gap and common source-credit constants')
    require(deep_payment == F(previous['exact_selected_deep_payment']), 'Same full selected cofactor-depth payment')

    rows, total_floors, total_increment_checks = [], 0, 0
    for index, spec in enumerate(specs[:41]):
        tag, zero = spec['tag'], spec['zero']
        f = lambda v: source.zero5_cost(tag, v)
        psi = lambda v: source.zero5_cost(zero, v)
        fm, pm = source.zero5_cost_metadata(tag), source.zero5_cost_metadata(zero)
        require(fm[0] == pm[0] == 1 and fm[1] == pm[1] >= 0 and spec['cofactor_count'] == 5,
                'Each complete source has the same affine-tail increment as its linear cost')
        entrance = max(3, fm[3], pm[3])
        increments, source_increments = [], []
        for v in range(1, entrance+2):
            vf, vp = f(v+1)-f(v), psi(v+1)-psi(v)
            require(0 <= vf <= vp, 'Every finite-prefix source increment pays the original event weight')
            if increments:
                require(increments[-1] <= vf, 'Discrete convexity through the affine entrance')
            increments.append(vf)
            source_increments.append(vp)
            total_increment_checks += 1
        require(increments[-1] == source_increments[-1] == fm[1], 'Both complete affine tails are retained')
        vmin, vmax = increments[0], increments[2]
        C = max(F(spec['joint']), max(f(v)+3*(f(v+1)-f(v)) for v in (1, 2, 3)))
        weight = group_weights[spec['name']] if index < 40 else identity_weight
        floors = 0
        for b, c5 in product(source.BASES, repeat=2):
            for j in range(5):
                v = f(b[j]+1)-f(b[j])
                k, t = C-f(b[j]), c5[j]*v
                require(0 <= vmin <= v <= vmax and 0 <= t-v <= t <= k,
                        'Both old and marked-event-removed floors are nonnegative')
                require(k/4-t/5 >= k/20 >= 0, 'Deep cap remains nonnegative throughout d>=1/4')
                require(0 <= v/5 <= vmax/5, 'Coordinatewise deep-max translation is bounded by vmax/5')
                floors += 1
        require(floors == 500 and weight > 0, 'All100 original layout pairs and all five cells')
        total_floors += floors
        gain = vmin*min_credit-vmax*deep_payment
        rows.append({'index': index, 'name': spec['name'], 'tuple': spec['tuple'], 'weight': weight,
                     'barrier': C, 'vmin': vmin, 'vmax': vmax, 'gain_before_residual': gain,
                     'residual_penalty': vmax*common_penalty, 'chosen': gain > 0,
                     'finite_prefix_and_tail': {'entrance': entrance, 'cost_increments': increments,
                                                'source_increments': source_increments, 'common_tail_increment': fm[1]},
                     'layout_cell_floor_checks': floors})
    require(total_floors == 20500 and tuple(row['index'] for row in rows if row['chosen']) == CHOSEN,
            'Fixed positive-gain subset of22 costs, with no source-dependent selection')
    for block in old49['frontier']['row_blocks']:
        for oldrow in block:
            require(len(oldrow['linear_directions']) == 41, 'Complete true conditional cost table')
            for row, direction in zip(rows, oldrow['linear_directions']):
                require(direction['index'] == row['index'] and F(direction['constant']) == row['barrier']
                        and F(direction['weight']) == row['weight'], 'Same original barriers and comparison weights at every refined vertex')

    chosen = [row for row in rows if row['chosen']]
    weighted_gain = sum(row['weight']*row['gain_before_residual'] for row in chosen)
    weighted_vmax = sum(row['weight']*row['vmax'] for row in chosen)
    penalty = common_penalty*weighted_vmax
    require(weighted_gain == F(161213733329143356587490859, 37528335927295467378374250000)
            and penalty == F(531765455625, 77286341132), 'Exact sum of all22 gains and the one combined residual penalty')
    K0, K74, K89 = F(current74['old_K']), F(current74['new_K']), F(previous['new_K'])
    A0, Acur = F(current74['signed_mass_coefficient']), F(current74['new_mass_coefficient'])
    gamma, q = F(current74['gamma_K']), F(23, 42)
    require(A0 >= Acur > penalty > 0 and 0 < K89 < K74 < K0,
            'Old signed mass absorbs all22 penalties together, before any target change')
    alternatives = {'outside_concentrated_faces': gamma*delta,
                    'large_best_slot_loss': Acur*rcut/5,
                    'all22_weighted_marker_gains': weighted_gain}
    reserve = min(alternatives.values())
    require(reserve == alternatives['outside_concentrated_faces'] > 0, 'Complete three-case global reserve')
    upper = F(current74['comparison_denominator_upper'])
    decrease = reserve/(2*upper)
    target = K0-decrease
    require(upper == F(5, 9) and decrease == F(9, 10)*reserve
            and target > source.WHOLE_CONST and A0-q*decrease > 0 and target < K89,
            'New global target starts from K0, retaining offset and mass sign')
    require(reserve-upper*decrease == reserve/2 > 0, 'Half the proved global reserve remains')
    fallbacks = []
    for row in current74['fallbacks']:
        bound = F(row['bound'])
        require(target > bound, 'Every complete old fallback stays below the new target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'new_gap': target-bound})
    cores = []
    for row in current74['complete_cores']:
        error = F(row['unchanged_error'])
        core_gap = target+error-403
        require(core_gap > 0, 'Both complete terminal comparisons remain open')
        cores.append({'box': row['box'], 'unchanged_error': error, 'combined_gap': core_gap})
    require(len(fallbacks) == 8 and len(cores) == 2 and F(current74['positive_survival_lower']) > 0,
            'Full source split, complete cores and inherited positive survival denominator')
    return {'schema': 'erdos7-weighted-marker-global-v1', 'source_sha256': used,
            'concentration_delta': delta, 'slot_loss_cutoff': rcut, 'source_loss_coefficient': source_weight,
            'general_gap_guards': guards, 'slot_gap_lower': gap,
            'common_residual_coefficient': common_penalty, 'best_slot_credit_lower': best_slot_credit,
            'minimum_source_credit': min_credit, 'selected_deep_payment': deep_payment,
            'cost_rows': rows, 'chosen_cost_indices': CHOSEN, 'chosen_cost_count': len(chosen),
            'total_layout_cell_floor_checks': total_floors, 'total_prefix_increment_checks': total_increment_checks,
            'weighted_gain_before_residual': weighted_gain, 'weighted_vmax': weighted_vmax,
            'combined_residual_penalty': penalty, 'conservative_mass_coefficient': Acur,
            'positive_remaining_mass_coefficient': Acur-penalty, 'three_case_reserves': alternatives,
            'global_signed_reserve_at_K0': reserve, 'old_K0': K0, 'previous_K89': K89,
            'decrease_from_K0': decrease, 'new_K': target, 'improvement_over89': K89-target,
            'improvement_over74': K74-target, 'new_signed_margin_lower': reserve/2,
            'new_mass_coefficient': A0-q*decrease, 'comparison_denominator_upper': upper,
            'positive_denominator_lower_factor': F(current74['positive_survival_lower']),
            'fallbacks': fallbacks, 'complete_cores': cores,
            'scope': 'Ordinary weighted original5 cancellation theorem for all41 linear costs. A fixed subset of22 improves the complete global K target from the original K0, without adding the preceding identity improvement. All independent original test labels, same actual source/carrier/deletion measures, combined deficiency charge, signed terms, infinite tails, eight fallbacks and two complete terminal comparisons retained. No Lean verification, sharpness or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('weighted_marker_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact weighted-marker global certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: all41 weighted costs,22 fixed gains, complete prefixes/tails, global comparison and eight fallbacks.')
    print('Global K <= '+str(float(F(result['new_K'])))+'; improvement over89 '+str(float(F(result['improvement_over89'])))+'.')


if __name__ == '__main__':
    main()
