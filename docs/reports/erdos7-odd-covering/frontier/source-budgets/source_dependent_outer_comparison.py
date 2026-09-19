#!/usr/bin/env python3
"""Keep source escape in46 credits and pay actual slot motion from one rho.

This is a complete candidate comparison with unchanged original tails and
fallbacks. It does not modify the canonical global comparison certificate.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/source_dependent_outer_comparison.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/source-budgets/shared_slot_gap_global.py': '9cf33d7af330eb181c7588b35f5be079187ffa8e192bce22bd7d3101c0b24a74',
    'certificates/source_norms/source-budgets/shared_slot_gap_global.json': 'c920fcbcf3b970dc9d41191db6ae7e22cf1cb03f141cf864c15388809d86d605',
    'frontier/source-budgets/shared_slot_defect_polytope.py': '36bbd9ef2f24a049893e4e5136c5afbed9279a0de5cfe607819a76cc91fe9c4f',
}
DELTA, R_CUT, DECREMENT = F(21, 500), F(3, 1000), F(137, 1000)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable pinned input')
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def original_credit(row, sigma, r, gap):
    w, vlo, vhi = (F(row[k]) for k in ('weight', 'vmin', 'vmax'))
    deep_coefficient = F(40, 3645) if row['quadratic'] else F(13, 1215)
    if F(row['old_fraction']) == 1:
        alpha = F(6, 5) if row['quadratic'] else F(1)
        value = vlo*min((alpha-(1+sigma)/5)*gap, F(1, 50)-r/5)-vhi*deep_coefficient/5
    else:
        value = vlo*min((1-sigma)*gap/5, F(1, 50)-r/5)
    return w*value


def calculate(base):
    io = module('source_outer_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/shared_slot_gap_global.json'))
    predecessor = module('source_outer_previous', base/'frontier/source-budgets/shared_slot_gap_global.py')
    require(encode(predecessor.calculate(base)) == previous,
            'All118 costs, choices, source constants, full tails and outer branches reconstruct')
    packing = module('source_outer_packing', base/'frontier/source-budgets/shared_slot_defect_polytope.py')
    guards = packing.concentrated_guards(DELTA, R_CUT)
    gap = guards['G_lower']
    rows = previous['cost_rows']
    A, a, b, gamma1, gamma2, K0 = (F(previous[k]) for k in (
        'conservative_mass_coefficient', 'S0_upper_constant', 'S0_upper_sigma_coefficient',
        'first_escape_gap', 'next_escape_gap', 'old_K0'))
    require((a, b) == (F(53, 360), F(5, 9)) and 0 < DELTA <= F(2, 27),
            'The same actual mass direction and the general packing domain')
    Vl, Vq, Vd, old_subtraction, L, P, Q = (F(0) for _ in range(7))
    transported = []
    for row in rows:
        w, vlo, vhi, C = (F(row[k]) for k in ('weight', 'vmin', 'vmax', 'barrier'))
        old = F(row['old_fraction']) == 1
        require(F(row['old_fraction'])+F(row['deep_fraction']) == 1,
                'Exactly the same one alternative for each original cost')
        sd = F(40, 3645) if row['quadratic'] else F(13, 1215)
        alpha = F(6, 5) if row['quadratic'] else F(1)
        slope = alpha-F(1, 5) if old else F(1, 5)
        minimum_slope = alpha-(1+DELTA)/5 if old else (1-DELTA)/5
        require(2*minimum_slope >= F(1, 5),
                'The gap movement price dominates the best-slot mass movement price')
        price = 2*w*vlo*slope
        L += price
        penalty = max(vhi, vlo/(9*gap)) if old else max(vhi, F(36, 25)*(vhi-vlo), vlo/(9*gap))
        P += w*penalty
        escape_penalty = F(0) if old else sd*C/4
        Q += w*escape_penalty
        if old:
            if row['quadratic']:
                Vq += w*vlo
            else:
                Vl += w*vlo
            old_subtraction += w*vhi*sd/5
        else:
            Vd += w*vlo
        transported.append({'index': row['index'], 'name': row['name'], 'tuple': row['tuple'],
                            'quadratic': row['quadratic'], 'weight': w,
                            'old_fraction': F(row['old_fraction']), 'deep_fraction': F(row['deep_fraction']),
                            'weighted_slot_motion_price': price, 'weighted_residual_penalty': w*penalty,
                            'weighted_escape_penalty': w*escape_penalty})
    require(len(rows) == 46 and Q == F(previous['combined_escape_penalty']),
            'All46 independent original tests; root-imbalance payment is unchanged')
    B0 = (8*Vl+2*Vd)/450+Vq/50-old_subtraction
    B1 = (6*Vl+3*Vd)/450
    B2 = (Vl+Vd)/450
    require(L == F(8, 5)*Vl+2*Vq+F(2, 5)*Vd,
            'The uniform slot-motion price matches the three source-independent groups')
    credit = lambda s: B0-B1*s+B2*s*s
    escape = lambda s: gamma2*s-(gamma2-gamma1)*s*s
    # Every identity below has a whole-interval analytic justification in147.
    gap_difference_at_delta = F(1, 90)-F(11, 45)*DELTA+DELTA*DELTA/24
    gap_difference_derivative_upper = -F(11, 45)+DELTA/12
    quadratic_uncapped_lower = (1-DELTA/5)*(F(1, 45)-DELTA/90)
    require(gap_difference_at_delta > 0 and gap_difference_derivative_upper < 0,
            'The beta guard is the minimum zero-slot-loss gap on the entire sigma interval')
    require(F(4, 225) < F(1, 50) and F(1, 225) < F(1, 50)
            and quadratic_uncapped_lower > F(1, 50),
            'The three source-credit formulas use the same fixed min branches throughout the interval')
    checks = []
    for sigma in (F(0), DELTA/2, DELTA):
        gap0 = packing.concentrated_guards(sigma, F(0))['G_lower']
        direct = sum(original_credit(row, sigma, F(0), gap0) for row in rows)
        require(gap0 == F(1, 45)-sigma/90 and direct == credit(sigma),
                'Exact original-cost evaluation agrees with the source polynomial')
        for r in (F(0), R_CUT/2, R_CUT):
            actual_gap = packing.concentrated_guards(sigma, r)['G_lower']
            moving = sum(original_credit(row, sigma, r, actual_gap) for row in rows)
            require(actual_gap >= gap0-2*r and moving >= credit(sigma)-L*r,
                    'Original minimum formulas agree with the proved slot-motion estimate')
            checks.append({'sigma': sigma, 'r': r, 'gap': actual_gap,
                           'weighted_credit': moving, 'slot_transport_slack': moving-credit(sigma)+L*r})
    require(sum(original_credit(row, F(previous['concentration_delta']), F(previous['slot_loss_cutoff']),
                                F(previous['slot_gap_lower'])) for row in rows) == F(previous['weighted_credit']),
            'The fixed original alternative choices recover118 exactly')
    residual = A-DECREMENT-P-5*L
    near_curvature = gamma2-gamma1-B2
    far_curvature = gamma2-gamma1-F(11, 36)*DECREMENT
    require(residual > 0 and near_curvature > 0 and far_curvature > 0,
            'One actual residual pays target, all cost penalties and the full r movement; all polynomials are concave')
    W = lambda s: escape(s)-DECREMENT*(a+b*s)
    R = lambda s: escape(s)-DECREMENT*(F(1, 4)+F(11, 36)*s*(1-s))
    margins = {'concentrated_small_r_zero_escape': credit(F(0))+W(F(0)),
               'concentrated_small_r_at_delta': credit(DELTA)-Q*DELTA+W(DELTA),
               'concentrated_large_r': (A-DECREMENT)*R_CUT/5-DECREMENT*(a+b*DELTA),
               'middle_at_delta': W(DELTA), 'middle_limit_at_half': W(F(1, 2)),
               'far_at_half': R(F(1, 2)), 'far_at_one': R(F(1))}
    require(len(margins) == 7 and min(margins.values()) > 0, 'All seven complete branch margins are strictly positive')
    target = K0-DECREMENT
    previous_target = F(previous['new_K'])
    require(previous_target-target == F(13, 1000) and target > 403,
            'The total decrement is counted once from K0; the candidate improvement over118 is exactly13/1000')
    fallbacks, cores = [], []
    for row in previous['fallbacks']:
        value = F(row['complete_bound'])
        require(value < target, 'Every complete original fallback remains below the candidate target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': value, 'candidate_target_gap': target-value})
    for row in previous['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and target+error-403 > 0, 'Both full terminal errors remain and the terminal gap is still positive')
        cores.append({'box': row['box'], 'unchanged_error': error, 'candidate_complete_gap': target+error-403})
    denominator_lower = F(previous['positive_denominator_lower_factor'])
    target_mass_coefficient = F(previous['old_mass_coefficient'])-F(23, 42)*DECREMENT
    require(len(fallbacks) == 8 and len(cores) == 2 and denominator_lower > 0 and target_mass_coefficient > 0,
            'Complete inherited branch counts, positive division and original coefficient sign')
    return encode({'schema': 'erdos7-source-dependent-outer-comparison-v1', 'source_sha256': PINS,
                   'delta': DELTA, 'slot_cutoff': R_CUT, 'decrement_from_K0': DECREMENT,
                   'packing_guards': guards, 'original_fixed_costs': transported,
                   'credit_groups': {'old_linear_vmin_sum': Vl, 'old_quadratic_vmin_sum': Vq,
                                     'deep_vmin_sum': Vd, 'old_deep_shift_subtraction': old_subtraction},
                   'zero_slot_credit_polynomial': {'constant': B0, 'negative_linear': B1, 'positive_quadratic': B2},
                   'slot_motion_price': L, 'slot_motion_residual_price': 5*L,
                   'uniform_cost_residual_penalty': P, 'unchanged_source_escape_penalty': Q,
                   'residual_after_target_cost_and_slot_payments': residual,
                   'near_negative_quadratic': near_curvature, 'far_negative_quadratic': far_curvature,
                   'zero_slot_guard_proof': {'Q_minus_beta_at_delta': gap_difference_at_delta,
                                            'Q_minus_beta_derivative_upper': gap_difference_derivative_upper,
                                            'quadratic_uncapped_lower': quadratic_uncapped_lower},
                   'exact_formula_checks': checks, 'signed_branch_margins': margins,
                   'strict_margin_lower': min(margins.values()),
                   'old_K0': K0, 'canonical118_K': previous_target,
                   'candidate_K': target, 'candidate_improvement_over118': previous_target-target,
                   'positive_denominator_lower_factor': denominator_lower,
                   'target_mass_coefficient': target_mass_coefficient,
                   'fallbacks': fallbacks, 'complete_cores': cores,
                   'scope': 'Ordinary full-source candidate comparison retaining118 fixed46 original alternatives and complete tails. The actual r motion of credits is paid once via r<=5rho after all cost and denominator charges. Source-dependent credits retain an explicit quadratic on the whole near interval; seven endpoints cover every source, with eight fallback branches and both terminal errors unchanged. Independent original labels and both orientations remain. Does not mutate the canonical globalK certificate; no Lean verification, optimality claim or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('source_outer_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Exact source-dependent complete outer comparison certificate')
    print('PASS: source-dependent credits, one actual residual, seven branches, eight fallbacks and both full errors.')
    print('Candidate K: '+result['candidate_K'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
