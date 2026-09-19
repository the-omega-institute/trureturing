#!/usr/bin/env python3
"""Consume the shared-deficit packing gap in the full global comparison.

Keep the original46 choices and fixed source rectangle; use the single
preselected decrement31/250 and check all seven complete branch margins.
"""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/shared_slot_gap_global.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/source-budgets/carrier_mass_global.py': '28d0419515b27fdb807474c451ab180039ba16c951c8554a1ff9ada418550d96',
    'certificates/source_norms/source-budgets/carrier_mass_global.json': '916809a16ff2d52ddbb62e63caf640c82a82f5be857916809c86922f8ec0d404',
    'frontier/source-budgets/shared_slot_defect_polytope.py': '4a775758d4f91f71b70783eddffde7f82e72d059db31b55547e74593b9e038ee',
    'certificates/source_norms/source-budgets/shared_slot_defect_polytope.json': '0d23f02c8f3d0f76cbcb4d6a428ac7070ad806fcec9d05ce3d4e46b1ca0134a1',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
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
    io = module('slot_gap_global_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name)))
    used = dict(PINS)
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    previous, packing = read('carrier_mass_global.json'), read('shared_slot_defect_polytope.json')
    for prior in (previous, packing):
        for path, pin in prior['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent inherited source')
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned inherited source: '+path)
            used[path] = pin
    predecessor = module('slot_gap_previous_global', base/'frontier/source-budgets/carrier_mass_global.py')
    require(encode(predecessor.calculate(base)) == previous, 'All previous complete branches and original46 choices reconstruct')
    gap_module = module('slot_gap_interface', base/'frontier/source-budgets/shared_slot_defect_polytope.py')
    require(encode(gap_module.calculate(base)) == packing, 'The new packing interface and its expanded r domain reconstruct')
    delta, rcut, decrease = F(1, 27), F(1, 520), F(31, 250)
    guards = gap_module.concentrated_guards(delta, rcut)
    require(encode(guards) == packing['concentrated_rectangle']
            and F(previous['concentration_delta']) == delta and F(previous['slot_loss_cutoff']) == rcut,
            'Keep precisely the old source rectangle; use the newly proved general packing guards')
    gap, old_gap = guards['G_lower'], F(previous['slot_gap_lower'])
    require(gap == F(2513, 126360) and gap-old_gap == F(1, 9477), 'Strict exact gap improvement')
    old_rows = read('shared_root_global.json')['cost_rows']
    generic_rows = read('shared_root_imbalance_payment.json')['cost_rows']
    penalty_module = module('slot_gap_deep_interface', base/'frontier/source-budgets/shared_root_imbalance_payment.py')
    old_indices, deep_indices = previous['fixed_old_indices'], previous['fixed_deep_indices']
    require(len(old_rows) == len(generic_rows) == 46 and len(old_indices) == 27 and len(deep_indices) == 19,
            'All original linear and quadratic costs and exactly the same fixed choices')
    best_credit, qstar, wdeep = F(1, 50)-rcut/5, (1+delta)/5, (1-delta)/5
    require(best_credit == guards['best_slot_credit_lower'] == F(51, 2600), 'Unchanged actual best-slot mass credit')
    rows = []
    for index, (old, generic) in enumerate(zip(old_rows, generic_rows)):
        require(old['index'] == generic['index'] == index, 'Original complete cost order')
        C, weight, vmin, vmax = (F(old[k]) for k in ('barrier', 'weight', 'vmin', 'vmax'))
        require(all(F(generic[k]) == F(old[k]) for k in ('barrier', 'weight', 'vmin', 'vmax')),
                'Same barriers, original increments and signed-comparison weights')
        alpha, sigmaD = (F(6, 5), F(40, 3645)) if old['quadratic'] else (F(1), F(13, 1215))
        require(F(generic['selected_deep_coefficient']) == sigmaD
                and sigmaD+F(generic['complete_remaining_mass_tail']) == F(1, 90), 'Complete selected and unselected pure3 families')
        old_credit = vmin*min((alpha-qstar)*gap, best_credit)-vmax*sigmaD/5
        old_penalty = max(vmax, vmin/(9*gap))
        coefficients = penalty_module.penalty_coefficients(vmin, vmax)
        deep_credit = vmin*min(wdeep*gap, best_credit)
        deep_penalty = max(coefficients['marked_base_penalty'], vmin/(9*gap))
        escape_penalty = sigmaD*C/4
        t_old, t_deep = F(int(index in old_indices)), F(int(index in deep_indices))
        require(t_old+t_deep == 1 and C >= 3*vmax >= coefficients['deep_capacity_penalty'],
                'One valid original alternative for each cost and the complete102 capacity theorem')
        credit, penalty = t_old*old_credit+t_deep*deep_credit, t_old*old_penalty+t_deep*deep_penalty
        require(credit > 0 and min(old_penalty, deep_penalty) > 0
                and old_credit >= F(old['old_credit']) and deep_credit >= F(old['deep_credit'])
                and old_penalty <= F(old['old_penalty']) and deep_penalty <= F(old['deep_penalty'])
                and escape_penalty == F(old['escape_penalty']), 'Stronger source credit, no larger residual charge, unchanged imbalance charge')
        rows.append({'index': index, 'name': old['name'], 'tuple': old['tuple'], 'quadratic': old['quadratic'],
                     'weight': weight, 'barrier': C, 'vmin': vmin, 'vmax': vmax,
                     'old_credit': old_credit, 'old_penalty': old_penalty,
                     'deep_credit': deep_credit, 'deep_penalty': deep_penalty, 'escape_penalty': escape_penalty,
                     'old_fraction': t_old, 'deep_fraction': t_deep,
                     'weighted_credit': weight*credit, 'weighted_residual_penalty': weight*penalty,
                     'weighted_escape_penalty': weight*t_deep*escape_penalty})
    B = sum(r['weighted_credit'] for r in rows)
    P = sum(r['weighted_residual_penalty'] for r in rows)
    Q = sum(r['weighted_escape_penalty'] for r in rows)
    old_B, old_P, old_Q = (F(previous[k]) for k in ('weighted_credit', 'combined_residual_penalty', 'combined_escape_penalty'))
    require(B > old_B and P < old_P and Q == old_Q, 'The improved gap produces a strict complete credit and residual improvement')
    a, b, c = (F(previous[k]) for k in ('S0_upper_constant', 'S0_upper_sigma_coefficient', 'E_upper_rho_coefficient'))
    A0, Acur = F(previous['old_mass_coefficient']), F(previous['conservative_mass_coefficient'])
    available = Acur-decrease*c
    require((a, b, c) == (F(53, 360), F(5, 9), F(1)) and A0 >= Acur and available > P > 0,
            'The denominator and all46 costs consume the same residual exactly once')
    gamma1, gamma2 = F(previous['first_escape_gap']), F(previous['next_escape_gap'])
    curvature, far_curvature = gamma2-gamma1, gamma2-gamma1-F(11, 36)*decrease
    require(0 < delta < F(1, 2) and 0 < gamma1 < gamma2 and far_curvature > 0,
            'Both retained escape polynomials are concave')
    W = lambda s: gamma2*s-curvature*s*s-decrease*(a+b*s)
    R = lambda s: -decrease/4+(gamma2-F(11, 36)*decrease)*s-far_curvature*s*s
    margins = {'concentrated_small_r_zero_escape': B+W(0),
               'concentrated_small_r_at_delta': B-Q*delta+W(delta),
               'concentrated_large_r': available*rcut/5-decrease*(a+b*delta),
               'middle_at_delta': W(delta), 'middle_limit_at_half': W(F(1, 2)),
               'far_at_half': R(F(1, 2)), 'far_at_one': R(1)}
    require(len(margins) == 7 and min(margins.values()) > 0, 'The preselected decrement passes all seven complete branches')
    # Attribution control: the new fixed target also has to be assessed with
    # the old gap, so unused old numerical room is not labelled new geometry.
    old_gap_margins = dict(margins)
    old_gap_margins['concentrated_small_r_zero_escape'] = old_B+W(0)
    old_gap_margins['concentrated_small_r_at_delta'] = old_B-old_Q*delta+W(delta)
    old_gap_target_valid = min(old_gap_margins.values()) > 0 and available > old_P
    K0, before = F(previous['old_K0']), F(previous['new_K'])
    target = K0-decrease
    require(before-target == F(1, 250) and target > 403, 'The full decrement is counted once from the original K0')
    fallbacks, cores = [], []
    for row in previous['fallbacks']:
        bound = F(row['complete_bound'])
        require(bound < target, 'Every complete fallback remains below the new target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'target_gap': target-bound})
    for row in previous['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and target+error > 403, 'Both full terminal errors retained')
        cores.append({'box': row['box'], 'unchanged_error': error, 'combined_gap': target+error-403})
    denominator_lower = F(previous['positive_denominator_lower_factor'])
    require(len(fallbacks) == 8 and len(cores) == 2 and denominator_lower > 0 and A0-F(23, 42)*decrease > 0,
            'Complete branch count, positive division and target sign')
    return {'schema': 'erdos7-shared-slot-gap-global-v1', 'source_sha256': used,
            'concentration_delta': delta, 'slot_loss_cutoff': rcut, 'source_guards': guards,
            'slot_gap_lower': gap, 'previous_slot_gap_lower': old_gap,
            'fixed_old_indices': old_indices, 'fixed_deep_indices': deep_indices, 'cost_rows': rows,
            'weighted_credit': B, 'combined_residual_penalty': P, 'combined_escape_penalty': Q,
            'credit_improvement_from_gap': B-old_B, 'residual_penalty_reduction_from_gap': old_P-P,
            'S0_upper_constant': a, 'S0_upper_sigma_coefficient': b, 'E_upper_rho_coefficient': c,
            'old_mass_coefficient': A0, 'conservative_mass_coefficient': Acur,
            'residual_after_denominator_charge': available, 'unused_residual_budget': available-P,
            'first_escape_gap': gamma1, 'next_escape_gap': gamma2,
            'middle_negative_quadratic': curvature, 'far_negative_quadratic': far_curvature,
            'signed_branch_margins': margins, 'strict_margin_lower': min(margins.values()),
            'same_target_with_previous_gap': {'valid': old_gap_target_valid, 'signed_branch_margins': old_gap_margins,
                                              'unused_residual_budget': available-old_P},
            'old_K0': K0, 'previous_K107': before, 'decrease_from_K0': decrease,
            'new_K': target, 'improvement_over107': before-target,
            'new_mass_coefficient': A0-F(23, 42)*decrease,
            'positive_denominator_lower_factor': denominator_lower, 'fallbacks': fallbacks, 'complete_cores': cores,
            'scope': 'Ordinary complete global comparison using117 stronger source packing on the entire original103/107 rectangle. All46 fixed alternatives, one actual residual, complete tails, seven branch margins, eight fallbacks and two terminal errors remain. The certificate separately tests whether the same target already follows with the old gap. No saturated-face extrapolation, Lean verification, optimality or unrestricted Erdos7 resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = encode(calculate(args.base))
    io = module('slot_gap_global_writer', args.base/'certificate_io.py')
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact shared-slot-gap full global certificate')
    if args.output is not None:
        io.write_certificate_text(args.output, json.dumps(result, indent=2)+'\n')
    print('PASS: stronger packing, all46 fixed costs, seven strict margins, eight complete fallbacks and two full errors.')
    with localcontext() as context:
        context.prec = 40
        for key in ('new_K', 'weighted_credit', 'combined_residual_penalty', 'strict_margin_lower'):
            value = F(result[key]); print(key+' '+str(Decimal(value.numerator)/Decimal(value.denominator)))
    print('Same target already valid with previous gap: '+str(result['same_target_with_previous_gap']['valid']))


if __name__ == '__main__':
    main()
