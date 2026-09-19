#!/usr/bin/env python3
"""Combine source-dependent complete credits with the product mass upper bound."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/product_source_outer_comparison.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/source_dependent_outer_comparison.py': 'b701b60a6d578e47f2463a087470d0d5ddbf041027c33c940f6bdfb1a7155757',
    'certificates/source_norms/source_dependent_outer_comparison.json': '9e126246b15c3af9e81df346bd0e07b240549cc31ecdbf517b774393f802c7ba',
    'frontier/product_coupled_carrier_mass.py': 'b6b7a61906ca5210ba0cb55f207d9d8221089bc65b92a1662820c2dd69966f3c',
    'certificates/source_norms/product_coupled_carrier_mass.json': 'add39ab619b7574d236b9e823467313137c3c5b020cf895960d3db0c1513d301',
}
DECREMENT = F(3, 20)


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


def calculate(base):
    io = module('product_source_io', base/'certificate_io.py')
    require('frontier/product_coupled_carrier_mass.py' in PINS
            and 'certificates/source_norms/product_coupled_carrier_mass.json' in PINS,
            'The complete product denominator theorem must be pinned before consumption')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    previous = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source_dependent_outer_comparison.json'))
    predecessor = module('product_source_previous', base/'frontier/source_dependent_outer_comparison.py')
    require(encode(predecessor.calculate(base)) == previous,
            'Reconstruct147 complete46-cost transport, original tails and all outside branches')
    source = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/shared_slot_gap_global.json'))
    mass = module('product_source_mass', base/'frontier/product_coupled_carrier_mass.py')
    mass_certificate = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/product_coupled_carrier_mass.json'))
    require(encode(mass.calculate(base)) == mass_certificate, 'The complete148 source and product-factor certificate reconstructs')
    early_limit, slope = F(mass.EARLY_LIMIT), F(mass.SLOPE)
    require((early_limit, slope) == (F(3, 61), F(61, 360)), 'Exact domain and coefficient of148')
    delta, rcut = F(previous['delta']), F(previous['slot_cutoff'])
    A, a, old_slope, gamma1, gamma2, K0 = (F(source[k]) for k in (
        'conservative_mass_coefficient', 'S0_upper_constant', 'S0_upper_sigma_coefficient',
        'first_escape_gap', 'next_escape_gap', 'old_K0'))
    B0, B1, B2 = (F(previous['zero_slot_credit_polynomial'][k]) for k in ('constant', 'negative_linear', 'positive_quadratic'))
    P, Q, slot_payment = (F(previous[k]) for k in ('uniform_cost_residual_penalty', 'unchanged_source_escape_penalty',
                                                 'slot_motion_residual_price'))
    require(0 < delta < early_limit < F(1, 2) and (delta, rcut) == (F(21, 500), F(3, 1000)),
            'Same source-dependent rectangle; the new denominator covers it and an early middle interval')
    for sigma in (F(0), delta, early_limit):
        for rho in (F(0), rcut/5):
            require(mass.bound_S0(sigma) == a+slope*sigma
                    and mass.bound_E(sigma, rho) == a+slope*sigma+rho,
                    'One unchanged actual residual in every application of the product denominator')
    escape = lambda s: gamma2*s-(gamma2-gamma1)*s*s
    credit = lambda s: B0-B1*s+B2*s*s
    rows = []

    def endpoint(name, reserve, payment):
        require(reserve > 0 and payment > 0, 'Positive complete reserve and target payment')
        rows.append({'branch': name, 'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                     'decrement_cap': reserve/payment, 'margin': reserve-DECREMENT*payment})

    endpoint('concentrated_small_r_zero_escape', B0, a)
    endpoint('concentrated_small_r_at_delta', credit(delta)-Q*delta+escape(delta), a+slope*delta)
    endpoint('concentrated_large_r', A*rcut/5, a+slope*delta+rcut/5)
    endpoint('early_middle_at_delta', escape(delta), a+slope*delta)
    endpoint('early_middle_at_product_limit', escape(early_limit), a+slope*early_limit)
    endpoint('old_middle_right_limit_at_product_limit', escape(early_limit), a+old_slope*early_limit)
    endpoint('old_middle_limit_at_half', escape(F(1, 2)), a+old_slope/2)
    endpoint('far_at_half', escape(F(1, 2)), F(1, 4)+F(11, 144))
    endpoint('far_at_one', gamma1, F(1, 4))
    require(len(rows) == 9 and min(r['margin'] for r in rows) > 0,
            'Every near and outside branch, including both sides of the product-boundary switch, is strictly positive')
    capacity = min(r['decrement_cap'] for r in rows)
    controls = [r['branch'] for r in rows if r['decrement_cap'] == capacity]
    require(controls == ['concentrated_small_r_at_delta'], 'The exact capacity of the stated fixed branch assignment')
    residual = A-DECREMENT-P-slot_payment
    capacity_residual = A-capacity-P-slot_payment
    near_curvature = gamma2-gamma1-B2
    far_curvature = gamma2-gamma1-F(11, 36)*capacity
    require(residual > 0 and capacity_residual > 0 and near_curvature > 0 and far_curvature > 0,
            'Same rho pays cost, actual slot motion and target; every polynomial remains concave through template capacity')
    target = K0-DECREMENT
    require(F(source['new_K'])-target == F(13, 500)
            and F(previous['candidate_K'])-target == F(13, 1000) and target > 403,
            'The total3/20 decrement is subtracted once from K0')
    fallbacks, cores = [], []
    for row in previous['fallbacks']:
        bound = F(row['complete_bound'])
        require(bound < target and bound < K0-capacity, 'All complete original fallback branches remain')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound,
                          'candidate_target_gap': target-bound, 'template_capacity_target_gap': K0-capacity-bound})
    for row in previous['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and K0-capacity+error-403 > 0, 'Both unchanged full terminal errors retain their sign')
        cores.append({'box': row['box'], 'unchanged_error': error,
                      'candidate_complete_gap': target+error-403, 'template_capacity_complete_gap': K0-capacity+error-403})
    denominator_lower = F(previous['positive_denominator_lower_factor'])
    target_coefficient = F(source['old_mass_coefficient'])-F(23, 42)*DECREMENT
    require(len(fallbacks) == 8 and len(cores) == 2 and denominator_lower > 0
            and F(source['old_mass_coefficient'])-F(23, 42)*capacity > 0,
            'Complete branch counts, original positive division and original target coefficient')
    return encode({'schema': 'erdos7-product-source-outer-comparison-v1', 'source_sha256': PINS,
                   'delta': delta, 'slot_cutoff': rcut, 'product_denominator_limit': early_limit,
                   'product_denominator_slope': slope, 'old_denominator_slope': old_slope,
                   'decrement_from_K0': DECREMENT, 'original_fixed_cost_count': len(previous['original_fixed_costs']),
                   'source_credit_polynomial': previous['zero_slot_credit_polynomial'],
                   'uniform_cost_residual_penalty': P, 'actual_slot_motion_residual_payment': slot_payment,
                   'unchanged_source_escape_penalty': Q, 'residual_after_all_charges': residual,
                   'near_negative_quadratic': near_curvature, 'complete_branch_endpoints': rows,
                   'strict_margin_lower': min(r['margin'] for r in rows),
                   'fixed_assignment_decrement_capacity': capacity, 'capacity_controlling_branches': controls,
                   'residual_at_capacity': capacity_residual,
                   'no_local_zero_escape_decrement_ceiling': B0/a,
                   'unchanged_far_endpoint_decrement_ceiling': 4*gamma1,
                   'old_K0': K0, 'canonical118_K': F(source['new_K']), 'candidate147_K': F(previous['candidate_K']),
                   'candidate_K': target, 'improvement_over118': F(source['new_K'])-target,
                   'improvement_over147': F(previous['candidate_K'])-target,
                   'positive_denominator_lower_factor': denominator_lower, 'target_mass_coefficient': target_coefficient,
                   'fallbacks': fallbacks, 'complete_cores': cores,
                   'scope': 'Ordinary full-source candidate comparison combining147 complete source-dependent46-cost credits with148 product-coupled upper mass bound on its exact sigma<=3/61 domain. One actual residual pays cost losses, actual r motion and target once. The early/old denominator switch is checked on both sides; nine endpoints, eight original fallback branches and both complete terminal errors remain. Capacity refers only to this fixed branch assignment and constants, not actual-family optimality. No canonical globalK mutation, Lean claim or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('product_source_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact product/source outer comparison certificate')
    print('PASS: product denominator, complete source credits, nine endpoints, eight fallbacks and two full errors.')
    print('Candidate K: '+result['candidate_K'])


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
