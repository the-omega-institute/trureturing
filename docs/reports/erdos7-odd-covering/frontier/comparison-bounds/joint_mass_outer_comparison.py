#!/usr/bin/env python3
"""Consume the signed actual-mass bound in every original global branch."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/joint_mass_outer_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/source-budgets/product_source_outer_comparison.py': '630c4a1eeb1a8ebd322e2ab0913a51e42093250d80c8971d28cfc21dd44dc32a', 'certificates/source_norms/source-budgets/product_source_outer_comparison.json': '58c6c7d82ab79261f0494918defc4c5203767d17c811ee38091f2c88df02ac02', 'frontier/source-budgets/joint_orientation_carrier_mass.py': '593bbb949c5d767b694c9b0ba96f03fab96028f5dc62b0da2684ae88f308d5a8', 'certificates/source_norms/source-budgets/joint_orientation_carrier_mass.json': '0b078075ea4af5500ec50f0a7ab10c30b104a45b537a7243b8f69ff4e8b2660a'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable input')
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
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('joint_outer_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    old = module('joint_outer_prior', base/'frontier/source-budgets/product_source_outer_comparison.py')
    previous = old.calculate(base)
    require(previous == json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/product_source_outer_comparison.json')),
            'Reconstruct149 including original46 costs, complete tails, outside branches and shared residual')
    mass = module('joint_outer_mass', base/'frontier/source-budgets/joint_orientation_carrier_mass.py')
    require(mass.calculate(base) == json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/joint_orientation_carrier_mass.json')),
            'Reconstruct154 signed actual-source mass proof inputs')
    source = json.loads(io.read_artifact_bytes(base/'certificates/source_norms/source-budgets/shared_slot_gap_global.json'))
    A, a, old_slope, gamma1, gamma2, K0 = (F(source[k]) for k in (
        'conservative_mass_coefficient', 'S0_upper_constant', 'S0_upper_sigma_coefficient',
        'first_escape_gap', 'next_escape_gap', 'old_K0'))
    delta, rcut = F(previous['delta']), F(previous['slot_cutoff'])
    limit, slope = mass.EARLY_LIMIT, mass.SLOPE
    require((delta, rcut, limit, slope) == (F(21, 500), F(3, 1000), F(1, 3), F(1, 10)),
            'Exact unchanged source domain and proved new mass domain')
    B0, B1, B2 = (F(previous['source_credit_polynomial'][k]) for k in ('constant', 'negative_linear', 'positive_quadratic'))
    P, Q, movement = (F(previous[k]) for k in ('uniform_cost_residual_penalty',
                         'unchanged_source_escape_penalty', 'actual_slot_motion_residual_payment'))
    decrement = B0/a
    escape = lambda s: gamma2*s-(gamma2-gamma1)*s*s
    credit = lambda s: B0-B1*s+B2*s*s
    rows = []

    def endpoint(name, reserve, payment):
        require(reserve > 0 and payment > 0, 'Positive endpoint quantities')
        rows.append({'branch': name, 'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                     'decrement_cap': reserve/payment, 'margin': reserve-decrement*payment})

    endpoint('concentrated_small_r_zero_escape', B0, mass.bound_E(0, 0))
    endpoint('concentrated_small_r_at_delta', credit(delta)-Q*delta+escape(delta), mass.bound_E(delta, 0))
    endpoint('concentrated_large_r', A*rcut/5, mass.bound_E(delta, rcut/5))
    endpoint('early_middle_at_delta', escape(delta), mass.bound_E(delta, 0))
    endpoint('early_middle_at_joint_limit', escape(limit), mass.bound_E(limit, 0))
    endpoint('old_middle_right_limit_at_joint_limit', escape(limit), a+old_slope*limit)
    endpoint('old_middle_limit_at_half', escape(F(1, 2)), a+old_slope/2)
    endpoint('far_at_half', escape(F(1, 2)), F(1, 4)+F(11, 144))
    endpoint('far_at_one', gamma1, F(1, 4))
    require(len(rows) == 9 and rows[0]['margin'] == 0 and min(r['margin'] for r in rows[1:]) > 0,
            'The exact zero-escape endpoint and all eight strict global endpoints')
    capacity = min(r['decrement_cap'] for r in rows)
    require(capacity == B0/a and [r['branch'] for r in rows if r['decrement_cap'] == capacity]
            == ['concentrated_small_r_zero_escape'], 'The unchanged zero-escape cost endpoint is now limiting')
    residual = A-decrement-P-movement
    require(A-capacity-P-movement > 0 and residual > 0 and gamma2-gamma1-B2 > 0
            and gamma2-gamma1-F(11, 36)*capacity > 0,
            'One residual pays all losses; all interval target functions remain concave through capacity')
    target = K0-decrement
    require(F(previous['candidate_K'])-target == decrement-F(previous['decrement_from_K0']) > 0,
            'Improvement over149 is counted once')
    fallbacks = []
    for row in previous['fallbacks']:
        bound = F(row['complete_bound'])
        require(bound < K0-capacity, 'Every original full fallback holds through capacity')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'candidate_target_gap': target-bound})
    cores = []
    for row in previous['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and K0-capacity+error > 403, 'The full terminal error remains and the goal is unresolved')
        cores.append({'box': row['box'], 'unchanged_error': error, 'candidate_complete_gap': target+error-403})
    positive_d = F(previous['positive_denominator_lower_factor'])
    require(len(fallbacks) == 8 and len(cores) == 2 and positive_d > 0
            and F(source['old_mass_coefficient'])-F(23, 42)*capacity > 0,
            'All branch counts and positive division remain valid')
    return encode({'schema': 'erdos7-joint-mass-outer-comparison-v1', 'source_sha256': PINS,
                   'delta': delta, 'slot_cutoff': rcut, 'signed_mass_limit': limit, 'signed_mass_slope': slope,
                   'decrement_from_K0': decrement, 'old_K0': K0, 'candidate_K': target,
                   'improvement_over149': F(previous['candidate_K'])-target, 'improvement_over118': F(source['new_K'])-target,
                   'original_fixed_cost_count': previous['original_fixed_cost_count'],
                   'source_credit_polynomial': previous['source_credit_polynomial'],
                   'residual_after_all_charges': residual, 'complete_branch_endpoints': rows,
                   'minimum_endpoint_margin': min(r['margin'] for r in rows),
                   'minimum_strict_endpoint_margin': min(r['margin'] for r in rows[1:]),
                   'fixed_assignment_decrement_capacity': capacity,
                   'capacity_controlling_branch': 'concentrated_small_r_zero_escape',
                   'unchanged_far_endpoint_decrement_ceiling': 4*gamma1,
                   'positive_denominator_lower_factor': positive_d, 'fallbacks': fallbacks, 'complete_cores': cores,
                   'scope': 'Ordinary full-source comparison using unchanged147 source-dependent46-cost credits and154 signed actual mass. All nine endpoints, eight fallbacks, both terminal errors and one actual residual remain. The gain uses the1/10 slope; the extension from6/49 to1/3 is not necessary for this decrement. Capacity is for this fixed branch assignment only. No canonical118 mutation, Lean or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('joint_outer_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete global comparison')
    print('PASS: signed mass, nine endpoints, eight fallbacks, two full errors; K='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
