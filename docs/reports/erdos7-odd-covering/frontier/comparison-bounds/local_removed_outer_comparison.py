#!/usr/bin/env python3
"""Use the complete160 local domain before evaluating the remaining155 branches."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/local_removed_outer_comparison.json'
PINS = {
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/comparison-bounds/joint_mass_outer_comparison.py': 'c637a858ab8fba9a0141378c353fb9fe8a3fadbff6c91d1e33e35b871d0cdc73',
    'certificates/source_norms/comparison-bounds/joint_mass_outer_comparison.json': 'a85c799a883b994348ef8495c4b2a19d380ca5cc5299ada0c6cce101cf1c2726',
    'frontier/comparison-bounds/residual_shell_k_comparison.py': '172e74c59a974c25ec9e77b4ee7cd2d4c84ac314f3cca4e3906160a7b065034b',
    'certificates/source_norms/comparison-bounds/residual_shell_k_comparison.json': '1e1b972b2756007c1f259232d4d03c49b527d5e88242b98e4300f48c3fa08f2f',
}


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    io = module('local_removed_io', base/'certificate_io.py')
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    prior_module = module('local_removed_prior', base/'frontier/comparison-bounds/joint_mass_outer_comparison.py')
    old = prior_module.calculate(base)
    require(old == read('joint_mass_outer_comparison'), 'Reconstruct all155 original outer data and complete tails')
    local = read('residual_shell_k_comparison')
    pins = {**local['source_sha256'], **old['source_sha256'], **PINS}
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source closure '+path)
    inner = read('product_source_outer_comparison')
    source = read('shared_slot_gap_global')
    A, a, b, gamma1, gamma2, K0 = (F(source[k]) for k in
        ('conservative_mass_coefficient', 'S0_upper_constant', 'S0_upper_sigma_coefficient',
         'first_escape_gap', 'next_escape_gap', 'old_K0'))
    old_delta, rcut, limit, slope = (F(old[k]) for k in
        ('delta', 'slot_cutoff', 'signed_mass_limit', 'signed_mass_slope'))
    sigma0, rho0, r0 = (F(local[k]) for k in
        ('source_radius', 'residual_radius', 'source_slot_loss_radius'))
    require((old_delta, rcut, limit, slope, sigma0, rho0, r0) ==
            (F(21, 500), F(3, 1000), F(1, 3), F(1, 10), F(1, 27), F(1, 1000), F(1, 520)),
            'Exact old outer partition and complete new local domain')
    require(0 < sigma0 < old_delta < limit < F(1, 2) and 0 < r0 < rcut and r0/5 < rho0,
            'Every local-complement interval and its shared-residual threshold')
    B0, B1, B2 = (F(old['source_credit_polynomial'][k]) for k in
        ('constant', 'negative_linear', 'positive_quadratic'))
    P, Q, L5 = (F(inner[k]) for k in
        ('uniform_cost_residual_penalty', 'unchanged_source_escape_penalty', 'actual_slot_motion_residual_payment'))
    escape = lambda s: gamma2*s-(gamma2-gamma1)*s*s
    credit = lambda s: B0-B1*s+B2*s*s
    marked = lambda s: credit(s)-Q*s+escape(s)
    mass = lambda s, rho=F(0): a+slope*s+rho
    crossing = lambda s: credit(s)-Q*s
    lower_cut, delta = F(41843898942, 10**12), F(41843898943, 10**12)
    require(sigma0 < lower_cut < delta < old_delta
            and crossing(lower_cut) > 0 > crossing(delta)
            and 2*B2*old_delta-B1-Q < 0,
            'One unique marked/unmarked crossing inside two exact adjacent rational cutoffs')
    nc, linear = gamma2-gamma1-B2, gamma2-B1-Q
    marked_derivative_numerator = lambda s: a*linear-slope*B0-2*a*nc*s-slope*nc*s*s
    unmarked_derivative_numerator = lambda s: a*gamma2-2*a*(gamma2-gamma1)*s-slope*(gamma2-gamma1)*s*s
    require(nc > 0 and marked_derivative_numerator(sigma0) < 0
            and unmarked_derivative_numerator(old_delta) > 0,
            'Marked capacity decreases and unmarked capacity increases throughout the tradeoff interval')
    ideal_capacity_upper = min(marked(lower_cut)/mass(lower_cut), escape(delta)/mass(delta))
    inherited_cut_capacity = min(marked(old_delta)/mass(old_delta), escape(old_delta)/mass(old_delta))
    rows = []

    def endpoint(name, reserve, payment, sigma=None, residual_lower=F(0)):
        require(reserve > 0 and payment > 0, 'Positive exact endpoint quantities')
        rows.append({'branch': name, 'sigma': sigma, 'residual_lower': residual_lower,
                     'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                     'decrement_cap': reserve/payment})

    for sigma, tag in ((sigma0, 'at_local_sigma'), (delta, 'at_delta')):
        endpoint('outer_small_r_strip_'+tag, marked(sigma), mass(sigma), sigma)
    for floor, branch in ((rho0, 'residual_above_local_radius'), (r0/5, 'slot_loss_above_local_radius')):
        for sigma, tag in ((F(0), 'at_zero_sigma'), (sigma0, 'at_local_sigma')):
            endpoint(branch+'_'+tag, marked(sigma)+(A-P-L5)*floor,
                     mass(sigma, floor), sigma, floor)
    endpoint('concentrated_large_r', A*rcut/5, mass(delta, rcut/5), delta, rcut/5)
    endpoint('early_middle_at_delta', escape(delta), mass(delta), delta)
    endpoint('early_middle_at_joint_limit', escape(limit), mass(limit), limit)
    endpoint('old_middle_right_limit_at_joint_limit', escape(limit), a+b*limit, limit)
    endpoint('old_middle_left_limit_at_half', escape(F(1, 2)), a+b/2, F(1, 2))
    endpoint('far_at_half', escape(F(1, 2)), F(1, 4)+F(11, 144), F(1, 2))
    endpoint('far_at_one', gamma1, F(1, 4), F(1))
    require(len(rows) == 13, 'Every endpoint of the complete actual-source complement')
    decrement = min(r['decrement_cap'] for r in rows)
    controlling = [r['branch'] for r in rows if r['decrement_cap'] == decrement]
    require(controlling == ['outer_small_r_strip_at_delta'], 'The zero-escape endpoint has been removed, exposing the outer strip')
    require(inherited_cut_capacity < decrement <= ideal_capacity_upper
            and ideal_capacity_upper-decrement < F(1, 10**12),
            'The new cutoff improves the inherited one and lies within the certified crossing-capacity bracket')
    for row in rows:
        row['margin'] = row['reserve_at_K0']-decrement*row['target_payment_coefficient']
    require(all(r['margin'] >= 0 for r in rows) and sum(r['margin'] == 0 for r in rows) == 1,
            'Exactly the stated outer endpoint is non-strict')
    residual = A-decrement-P-L5
    require(residual > 0 and A-decrement > 0 and gamma2-gamma1-B2 > 0
            and gamma2-gamma1-F(11, 36)*decrement > 0,
            'One actual residual pays all losses and every interval target function is concave')
    target = K0-decrement
    local_rows = []
    for shell in local['shells']:
        comparison = shell['comparison']
        bound = F(comparison['comparison_upper'])
        require(comparison['all_original_indices'] == list(range(52))
                and F(comparison['remaining_S_coefficient']) > 0
                and F(comparison['margin_at509_on_shell']) >= 0 and bound <= 509 < target,
                'Every complete local52-cost shell is strictly below the new global target')
        local_rows.append({'rho_lower': F(comparison['residual_lower']), 'rho_upper': F(comparison['residual_upper']),
                           'complete_bound': bound, 'global_target_gap': target-bound})
    require(local_rows[0]['rho_lower'] == 0 and local_rows[0]['rho_upper'] == local_rows[1]['rho_lower']
            and local_rows[1]['rho_upper'] == rho0, 'Every residual in the local source domain is covered')
    fallbacks = []
    for row in old['fallbacks']:
        bound = F(row['complete_bound'])
        require(bound < target, 'Unchanged full original fallback')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'candidate_target_gap': target-bound})
    cores = []
    for row in old['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and target+error-403 > 0, 'Both full terminal errors remain; unrestricted goal is open')
        cores.append({'box': row['box'], 'unchanged_error': error, 'candidate_complete_gap': target+error-403})
    require(len(fallbacks) == 8 and len(cores) == 2 and len(local_rows) == 2
            and F(old['positive_denominator_lower_factor']) > 0
            and F(source['old_mass_coefficient'])-F(23, 42)*decrement > 0,
            'All branches and positive division are preserved')
    improvement = F(old['candidate_K'])-target
    require(improvement > 0 and decrement > B0/a, 'The old zero-escape ceiling is genuinely exceeded')
    return encode({'schema': 'erdos7-local-removed-outer-comparison-v1', 'source_sha256': pins,
                   'local_source_radius': sigma0, 'local_residual_radius': rho0, 'local_slot_radius': r0,
                   'outer_delta': delta, 'outer_slot_cutoff': rcut, 'signed_mass_limit': limit,
                   'cutoff_tradeoff': {'old_cutoff': old_delta, 'root_lower': lower_cut, 'root_upper': delta,
                                       'crossing_at_lower': crossing(lower_cut), 'crossing_at_upper': crossing(delta),
                                       'marked_capacity_derivative_upper_numerator': marked_derivative_numerator(sigma0),
                                       'unmarked_capacity_derivative_lower_numerator': unmarked_derivative_numerator(old_delta),
                                       'old_cutoff_capacity': inherited_cut_capacity,
                                       'ideal_crossing_capacity_upper': ideal_capacity_upper,
                                       'capacity_distance_upper': ideal_capacity_upper-decrement},
                   'signed_mass_slope': slope, 'old_K0': K0, 'decrement_from_K0': decrement,
                   'candidate_K': target, 'improvement_over155': improvement,
                   'original_fixed_outer_cost_count': old['original_fixed_cost_count'],
                   'outer_credit_polynomial': old['source_credit_polynomial'],
                   'residual_after_all_charges': residual, 'complete_outer_endpoints': rows,
                   'capacity_controlling_branches': controlling, 'local_complete_shells': local_rows,
                   'fallbacks': fallbacks, 'complete_cores': cores,
                   'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
                   'old_zero_escape_capacity': B0/a, 'fixed_assignment_decrement_capacity': decrement,
                   'unchanged_far_endpoint_decrement_ceiling': 4*gamma1,
                   'scope': 'Ordinary full-source comparison. The entire160 local rectangle is consumed only on its own actual source; its complement uses155 unchanged46-cost credits, complete tails, thirteen endpoints, eight fallbacks and two terminal errors. One actual rho, with r<=5rho. The limiting outer strip belongs to this fixed partition, not an optimality statement. No canonical globalK mutation, Lean theorem or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('local_removed_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete local-complement certificate')
    print('PASS: local160 plus its full actual-source complement; K<='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
