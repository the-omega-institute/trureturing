#!/usr/bin/env python3
"""Cancel the old shallow payment for one retained original5 event; improve K.

The ordinary proof removes exactly one event from the identity floor and
retains its actual surviving mass. The old carrier cap changes by an
explicit affine term independent of both original test layouts. Its shallow
part cancels against the same actual virtual deletion, leaving only the
selected deep payment. Complete tails, signed terms and fallbacks remain.
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
CERTIFICATE = 'certificates/source_norms/endpoint-bounds/broad_marked_identity_global.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/endpoint-bounds/broad_five_slot_tradeoff.py': '73a23d45c240ac9cd59216243127030e86f188d7dca930f689c44437799c59c5',
    'certificates/source_norms/endpoint-bounds/broad_five_slot_tradeoff.json': '563dd67bdd067108b08c0f9290d55271104559c1b01af7ba97cb61f97a6dc15c',
    'frontier/source-budgets/global_k_face_gain.py': 'c812fd6aba07ba15f100c85e85595661b8447448f67a6c0d95a1c9a1861ad96d',
    'certificates/source_norms/source-budgets/global_k_face_gain.json': '124d4428a67f5193f3814849c527e30c331a0757328836756aec088a87fdcbc8',
    'frontier/source-budgets/full_linear_carrier_frontier.py': '98cbec50d807ed9208504c8cd2384659a4300d6909d54414e5e2156285298888',
    'frontier/source-budgets/shared_linear_refinement.py': '2150065bb9eb9369847cf399e9f14b78406b4aecfaa2da10ea2d00eff8d0fe7e',
    'certificates/source_norms/source-budgets/full_linear_carrier_frontier.json': '98631aaec7edbf0bbec41befad13df4ae9bcab2f6163675da10d8d7c9273c44c',
}


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
    io = module('marked_global_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    broad = read('certificates/source_norms/endpoint-bounds/broad_five_slot_tradeoff.json')
    current = read('certificates/source_norms/source-budgets/global_k_face_gain.json')
    old49 = read('certificates/source_norms/source-budgets/full_linear_carrier_frontier.json')
    for record in (broad, current, old49):
        for path, pin in record['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited input')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited source: '+path)
            used[path] = pin
    source = module('marked_global_source', base/'verify_joint_frontier.py')
    schedule = module('marked_global_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('marked_global_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    carrier = module('marked_global_carrier', base/'frontier/source-budgets/full_linear_carrier_frontier.py')
    specs, groups, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    spec = specs[40]
    require(len(specs) == 46 and spec['tag'] == ('h', F(0)) and spec['cofactor_count'] == 5,
            'The live direction is exactly identity with five selected cofactors')
    metadata = source.zero5_cost_metadata(spec['zero'])
    require(metadata[0:3] == (1, F(1), F(-1)), 'The complete selected source tail is exactly v-1')
    for v in range(1, metadata[3]+2):
        require(source.zero5_cost(spec['tag'], v) == v
                and source.zero5_cost(spec['zero'], v) == v-1, 'Identity and selected-source values up to the affine tail')
    beta = sum({'R17': F(1), 'R19': source.P17, 'R5': source.EXTRA5}[g['name']]*g['tail_coefficient'] for g in groups)
    require(beta == F(current['identity_cost_coefficient']) == F(94212612766226, 1174116234095805) > 0,
            'Complete positive identity comparison coefficient')
    C = F(6)
    for block in old49['frontier']['row_blocks']:
        for row in block:
            direction = row['linear_directions'][40]
            require(F(direction['constant']) == C and F(direction['weight']) == beta, 'The same fixed live barrier at every refined row')

    # Exhaust all finite floors. The subsequent affine cap identity is
    # independent of source parameters and holds before layout maximization.
    floor_checks = 0
    for item, c5 in product(spec['layouts'], source.BASES):
        b, increments = item['baseline'], item['joint'][1]
        require(tuple(increments) == (F(1),)*5, 'Every marked source increment is exactly one')
        for j in range(5):
            k, correction = C-b[j], F(c5[j])
            require(0 <= correction-1 <= correction <= k
                    and k-correction >= 0 and k-(correction-1) >= 0,
                    'Original and one-event-removed floors stay nonnegative')
            require(k*F(1, 4)-correction/5 >= k/20,
                    'Selected deep remainder is nonnegative throughout d>=1/4')
            floor_checks += 1
    require(floor_checks == 500, 'All100 original layout pairs and five ternary cells')
    selected = sum(F(1, 3**a) for a in range(3, 6))
    remaining = F(1, 3**6)/(1-F(1, 3))
    seven_sum = F(6, 5)*F(1, 7)/(1-F(1, 7))
    require((selected, remaining, seven_sum) == (F(13, 243), F(1, 486), F(1, 5))
            and selected+remaining == F(1, 18), 'All selected and unselected pure3 and seven tails are complete')
    roots = (0, 0, 1, 1, 1)
    require(tuple(carrier.CARRIERS) == tuple(product((-1, 0, 1), (-1, 0, 1, 2, 3, 4))), 'All18 carriers including empty components')
    shifts = []
    for r, cell in carrier.CARRIERS:
        # This affine expression is the exact change after the outside1/5.
        coefficients = tuple(F(int(r != -1 and roots[j] == r)+int(cell == j), 25) for j in range(5))
        shifts.append({'carrier': (r, cell), 'eta_coefficients': coefficients, 'constant': selected/25})
    cap = (F(1, 3)+F(1, 9)+selected)/25
    direct = seven_sum*sum(F(1, 3**a) for a in range(1, 6))/5
    require(cap == direct == F(121, 6075), 'Uniform old marked payment from all five original cofactor depths')
    eta_vertices = [(F(1, 9),)*5]+[tuple(F(1, 18) if j == k else F(1, 9) for j in range(5)) for k in range(5)]
    shift_values = [row['constant']+sum(a*b for a, b in zip(row['eta_coefficients'], eta))
                    for row, eta in product(shifts, eta_vertices)]
    require(min(shift_values) >= 0 and max(shift_values) == cap, 'Exact affine payment bound on the whole deficit simplex')

    K0, K74 = F(current['old_K']), F(current['new_K'])
    A0, Acur = F(current['signed_mass_coefficient']), F(current['new_mass_coefficient'])
    gamma = F(current['gamma_K'])
    previous_drop = F(current['strict_decrease'])
    q, E_upper = F(23, 42), F(current['comparison_denominator_upper'])
    require(K0-K74 == previous_drop > 0 and Acur == A0-q*previous_drop > 0 and E_upper == F(5, 9),
            'Use the current smaller mass coefficient conservatively at the old target')
    zeta0, r0, g0, c0 = F(25, 27), F(1, 12000), F(397, 36000), F(4000, 397)
    require(F(broad['concentration']['zeta_lower']) == zeta0
            and F(broad['slab']['r_split']) == r0
            and F(broad['slab']['source_slot_gap_lower']) == g0
            and F(broad['slab']['residual_coefficient_upper']) == c0,
            'Exactly the established whole-slab source constants')
    shallow_density_cap = 2*seven_sum
    source_loss_coefficient = 1-shallow_density_cap
    deep_payment = selected/25
    uniform_slot_credit = source_loss_coefficient*g0
    gain = uniform_slot_credit-deep_payment
    require((shallow_density_cap, source_loss_coefficient, deep_payment, gain)
            == (F(2, 5), F(3, 5), F(13, 6075), F(21757, 4860000)) and gain > 0,
            'Only the selected deep payment remains after exact shallow cancellation')
    Delta_max = 3*(1-zeta0)/4
    require(Delta_max == F(1, 18), 'Complete zero-box concentration implies the whole broad slab')
    best_slot_mass_over5 = F(1, 50)-r0/5
    require(best_slot_mass_over5 == F(1199, 60000) > uniform_slot_credit,
            'The best-slot virtual5 payment exceeds the uniform other-slot credit')
    require(F(broad['slab']['m_over5_lower']) == best_slot_mass_over5
            and F(broad['slab']['delta_upper']) == Delta_max
            and F(broad['slab']['large_r_mass_residual_lower']) == r0/5,
            'The same complete best-slot, slab and actual-mass branches')
    require(F(1, 9)/g0 == c0 > 1 and Acur-beta*c0 > 0,
            'The single actual deficiency penalty is absorbed by the signed mass coefficient')
    broad_mass_slope = Acur-beta*c0
    broad_reserve = beta*gain
    require(broad_reserve == F(1024891907977389541, 2853102448852806150000), 'Exact broad-slab marked-event reserve')

    # Concentration constrains the same actual shallow carrier mixture.
    # The distinguished root and cell on either controlling face are disjoint.
    concentration_delta, refined_r = F(13, 500), F(1, 8000)
    refined_weight = 1-(1+concentration_delta)/5
    refined_eta = F(1, 9)-concentration_delta/18
    refined_h1 = F(1, 3)-concentration_delta/6
    refined_Delta = 3*concentration_delta/4
    refined_guards = {'pure5_slot': F(1, 10)-refined_r,
                      'alpha_slot': refined_h1/5-refined_r,
                      'beta_slot': refined_eta/5-refined_r,
                      'remaining_slot': refined_h1*(F(1, 10)-refined_Delta)-2*refined_r}
    refined_gap = min(refined_guards.values())
    refined_c = max(F(1), F(1, 9)/refined_gap)
    refined_gain = refined_weight*refined_gap-deep_payment
    require(concentration_delta < F(1, 2) and refined_Delta < Delta_max
            and refined_r < min(F(1, 10), refined_h1/5, refined_eta/5),
            'General source-packing hypotheses at the larger slot-loss cutoff')
    require((refined_weight, refined_gap, refined_c, refined_gain)
            == (F(1987, 2500), F(2617, 120000), F(40000, 7851), F(369198299, 24300000000)),
            'Exact concentration, carrier-density and general-gap constants')
    require(F(1, 50)-refined_r/5 > refined_weight*refined_gap,
            'Best-slot5 deletion also exceeds the refined other-slot credit')
    for distinguished in ((1, 0), (1, 1)):
        require(all(int(roots[j] == distinguished[0])+int(j == distinguished[1]) <= 1 for j in range(5)),
                'Each controlling shallow carrier consists of disjoint root and cell')
    mass_slope = Acur-beta*refined_c
    require(mass_slope > 0, 'Actual mass absorbs the refined common deficiency coefficient')
    reserve = beta*refined_gain
    require(reserve == F(1023033422871656583811, 839147779074354750000000), 'Exact improved global reserve')
    alternatives = {'outside_concentrated_zero_faces': gamma*concentration_delta,
                    'large_best_slot_loss': Acur*refined_r/5,
                    'concentrated_small_slot_loss': reserve}
    require(min(alternatives.values()) == reserve > 0, 'All actual effective9 cases share the same positive reserve')
    current_reserve = reserve-E_upper*previous_drop
    require(current_reserve > 0, 'Positive reserve remains at the preceding published target')
    decrease = reserve/(2*E_upper)
    target = K0-decrease
    gain74 = K74-target
    require(decrease == F(9, 10)*reserve
            and gain74 > 0 and target > source.WHOLE_CONST and A0-q*decrease > 0,
            'Strictly improved global target with all original sign branches')
    require(reserve-E_upper*decrease == reserve/2 > 0, 'Half the proved reserve remains at the new target')
    fallbacks = []
    for row in current['fallbacks']:
        bound = F(row['bound'])
        require(target > bound and K74-bound == F(row['new_gap']), 'Unchanged complete fallback still below the new target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'new_gap': target-bound})
    require(len(fallbacks) == 8, 'All eight other source branches retained')
    cores = []
    for row in current['complete_cores']:
        error = F(row['unchanged_error'])
        gap = target+error-403
        require(gap == F(row['new_combined_gap'])-gain74 > 0, 'Both complete terminal gaps remain open')
        cores.append({'box': row['box'], 'unchanged_error': error, 'combined_gap': gap})
    require(len(cores) == 2 and F(current['positive_survival_lower']) > 0, 'Both terminal cores and prior positive denominator')
    return {'schema': 'erdos7-broad-marked-identity-global-v1', 'source_sha256': used,
            'identity_direction': 40, 'barrier': C, 'identity_cost_coefficient': beta,
            'fixed_layout_floor_checks': floor_checks, 'selected_pure3_depths': [1, 2, 3, 4, 5],
            'selected_deep_sum': selected, 'remaining_pure3_tail': remaining, 'complete_seven_sum': seven_sum,
            'exact_carrier_payment_shifts': shifts, 'uniform_old_marked_payment': cap,
            'exact_selected_deep_payment': deep_payment, 'shallow_virtual_density_upper': shallow_density_cap,
            'retained_source_loss_coefficient': source_loss_coefficient, 'uniform_slot_credit': uniform_slot_credit,
            'best_slot_mass_over5_lower': best_slot_mass_over5, 'uniform_marked_gain_before_residual': gain,
            'zero_box_mass_cutoff': zeta0, 'slab_deficit_upper': Delta_max,
            'best_slot_loss_cutoff': r0, 'uniform_slot_gap_lower': g0,
            'common_residual_coefficient': c0, 'conservative_mass_coefficient': Acur,
            'broad_positive_residual_slope': broad_mass_slope, 'broad_signed_reserve': broad_reserve,
            'refined_concentration_delta': concentration_delta, 'refined_slot_loss_cutoff': refined_r,
            'refined_source_loss_coefficient': refined_weight, 'refined_gap_guards': refined_guards,
            'refined_slot_gap_lower': refined_gap, 'refined_common_residual_coefficient': refined_c,
            'refined_marked_gain_before_residual': refined_gain, 'positive_residual_slope': mass_slope,
            'gamma_K': gamma, 'three_case_reserves': alternatives,
            'global_signed_reserve_at_K0': reserve, 'reserve_at_previous_target': current_reserve,
            'old_K0': K0, 'previous_K74': K74, 'decrease_from_K0': decrease, 'improvement_over74': gain74,
            'new_K': target, 'positive_denominator_lower_factor': F(current['positive_survival_lower']),
            'comparison_denominator_upper': E_upper, 'new_signed_margin_lower': reserve/2,
            'new_mass_coefficient': A0-q*decrease, 'fallbacks': fallbacks, 'complete_cores': cores,
            'scope': 'Ordinary full-domain K theorem, with all eight fallback branches. Retains exactly one original zero-seven modulus5 event and cancels its old shallow carrier payment against the same actual virtual deletion. Subtracts the remaining complete selected deep payment. Uses profile85 broad-slab source packing with one cap/union deficiency. Same actual mass, independent labels, all source and AP exponent tails and prior signed comparison. No sharpness, Lean verification or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('marked_global_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete global marked-event certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: retained original5 event, exact old cap shift, complete tails, global reserve and all eight fallbacks.')
    print('Global K <= '+str(float(F(result['new_K'])))+'; improvement over74 '+str(float(F(result['improvement_over74'])))+'.')


if __name__ == '__main__':
    main()
