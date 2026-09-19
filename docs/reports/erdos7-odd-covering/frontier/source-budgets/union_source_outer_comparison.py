#!/usr/bin/env python3
"""Join two complete actual-source neighborhoods before global comparison."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/union_source_outer_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/comparison-bounds/local_removed_outer_comparison.py': '9c4554cadb43746087c315de12d45957b45bab9b3273c5150aeae3edaf8269de', 'certificates/source_norms/comparison-bounds/local_removed_outer_comparison.json': '358dc8ae38eaa37d2274eeb16e0058f1e820c132df10bba14ccf836928ce074c', 'frontier/comparison-bounds/pure_five_complete_face_comparison.py': '45c1b016e68eb5397a78a6540c4f8ee5287c214b6bb35625d4d0232224dd2314', 'certificates/source_norms/comparison-bounds/pure_five_complete_face_comparison.json': 'e0d124f375efa0567777973a2ba468d368285807aed054ada2e57727b896d4f2', 'frontier/source-budgets/expanded_source_complete_comparison.py': 'd5eaeb60aa63d06c8b0d515079d51f7dc76444d91182ef1ac9a286ffe184b50b', 'certificates/source_norms/source-budgets/expanded_source_complete_comparison.json': '6d8f932978592866152090674c87ab68989f1c4b0a0b348faebf7c5f61972ac6'}


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
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(PINS, 'Complete new source result must be pinned before consumption')
    io = module('union_source_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    inputs = {name: read(name) for name in ('local_removed_outer_comparison', 'pure_five_complete_face_comparison',
                                         'expanded_source_complete_comparison')}
    pins = dict(PINS)
    for entry in inputs.values():
        for path, pin in entry['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original source closure '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    old = module('union_source_old', base/'frontier/comparison-bounds/local_removed_outer_comparison.py').calculate(base)
    require(old == inputs['local_removed_outer_comparison'], 'Reconstruct the preceding full global partition')
    local = inputs['pure_five_complete_face_comparison']['complete_neighborhood_transport']
    expanded = inputs['expanded_source_complete_comparison']['expanded_residual_comparison']
    par = {key: F(expanded['parameters'][key]) for key in ('delta', 'rho', 'rbar')}
    s0, R0, r0, s1, R1 = F(1, 27), F(1, 1000), F(1, 520), par['delta'], par['rho']
    require((s1, R1, par['rbar']) == (F(1, 22), F(1, 15000), F(1, 3000)),
            'Exact new complete source/residual domain')
    require(0 < R1 < r0/5 < R0 and s0 < s1 < F(1, 3), 'Two overlapping complete actual-source rectangles')
    src, outer = read('shared_slot_gap_global'), read('product_source_outer_comparison')
    A, a, b, gamma1, gamma2, K0 = (F(src[k]) for k in
        ('conservative_mass_coefficient', 'S0_upper_constant', 'S0_upper_sigma_coefficient',
         'first_escape_gap', 'next_escape_gap', 'old_K0'))
    old_outer = read('joint_mass_outer_comparison')
    B0, B1, B2 = (F(old_outer['source_credit_polynomial'][k]) for k in
        ('constant', 'negative_linear', 'positive_quadratic'))
    P, Q, L5 = (F(outer[k]) for k in
        ('uniform_cost_residual_penalty', 'unchanged_source_escape_penalty', 'actual_slot_motion_residual_payment'))
    rcut, limit, slope = F(3, 1000), F(1, 3), F(1, 10)
    require(s0 < F(old_outer['delta']) and r0 < rcut == F(old_outer['slot_cutoff'])
            and limit == F(old_outer['signed_mass_limit']) and slope == F(old_outer['signed_mass_slope']),
            'The entire marked region is inside its original proved domain')
    escape = lambda s: gamma2*s-(gamma2-gamma1)*s*s
    marked = lambda s: B0-B1*s+B2*s*s-Q*s+escape(s)
    mass = lambda s, u=F(0): a+slope*s+u
    floor = min(R0, r0/5)
    require(floor == F(1, 2600), 'Outside the old rectangle, r<=5rho forces this same residual floor')
    rows = []

    def endpoint(branch, sigma, reserve, payment, residual_lower=F(0)):
        require(reserve > 0 and payment > 0, 'Positive full endpoint quantities')
        rows.append({'branch': branch, 'sigma': sigma, 'residual_lower': residual_lower,
                     'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                     'decrement_capacity': reserve/payment})

    for s, tag in ((F(0), 'zero'), (s0, 'old_source_radius')):
        endpoint('low_source_marked_'+tag, s, marked(s)+(A-P-L5)*floor, mass(s, floor), floor)
    endpoint('low_source_large_r', s0, A*rcut/5, mass(s0, rcut/5), rcut/5)
    for s, tag in ((s0, 'old_source_radius'), (s1, 'new_source_radius')):
        endpoint('residual_bridge_'+tag, s, escape(s)+A*R1, mass(s, R1), R1)
    for s, tag in ((s1, 'new_source_radius'), (limit, 'joint_limit')):
        endpoint('early_middle_'+tag, s, escape(s), mass(s))
    for s, tag in ((limit, 'joint_limit'), (F(1, 2), 'half')):
        endpoint('old_middle_'+tag, s, escape(s), a+b*s)
    for s, tag in ((F(1, 2), 'half'), (F(1), 'one')):
        endpoint('far_'+tag, s, escape(s), F(1, 4)+F(11, 36)*s*(1-s))
    require(len(rows) == 11, 'All endpoints of six exhaustive outside source regions')
    h = min(r['decrement_capacity'] for r in rows)
    controlling = [r['branch'] for r in rows if r['decrement_capacity'] == h]
    require(controlling == ['low_source_marked_zero'], 'The old crossing is removed; the original slot-loss boundary controls')
    for row in rows:
        row['margin'] = row['reserve_at_K0']-h*row['target_payment_coefficient']
    require(sum(r['margin'] == 0 for r in rows) == 1 and all(r['margin'] >= 0 for r in rows),
            'Every entire interval has its required nonnegative endpoints')
    require(gamma2-gamma1-B2 > 0 and gamma2-gamma1-F(11, 36)*h > 0
            and A-h-P-L5 > 0 and A-h > 0, 'Concavity and one common residual justify all reductions')
    target = K0-h
    local_rows = []
    for shell in local['shells']:
        upper = F(shell['comparison_upper'])
        require(shell['all_original_indices'] == list(range(52))
                and F(shell['remaining_S_coefficient']) > 0 and upper < target,
                'Both complete old-domain shells hold strictly below the global target')
        local_rows.append({'rho_lower': F(shell['residual_lower']), 'rho_upper': F(shell['parameters']['rho']),
                           'source_radius': F(shell['parameters']['delta']), 'complete_bound': upper})
    require(len(local_rows) == 2 and local_rows[0]['rho_lower'] == 0
            and local_rows[0]['rho_upper'] == local_rows[1]['rho_lower']
            and local_rows[1]['rho_upper'] == R0 and all(r['source_radius'] == s0 for r in local_rows),
            'The first complete local domain has no residual gap')
    new_comparison = expanded['comparison']
    new_bound = F(new_comparison['comparison_upper'])
    require(new_comparison['all_original_indices'] == list(range(52))
            and F(new_comparison['remaining_S_coefficient']) > 0
            and F(new_comparison['denominator_at_mass_floor']) > 0 and new_bound < target,
            'The new complete52-cost comparison applies on its whole actual-source rectangle')
    local_rows.append({'rho_lower': F(0), 'rho_upper': R1, 'source_radius': s1, 'complete_bound': new_bound})
    fallbacks = []
    for row in old['fallbacks']:
        bound = F(row['complete_bound'])
        require(bound < target, 'Original complete fallback remains valid')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'candidate_target_gap': target-bound})
    cores = []
    for row in old['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and target+error-403 > 0, 'Both complete terminal errors remain; no unrestricted solution')
        cores.append({'box': row['box'], 'unchanged_error': error, 'candidate_complete_gap': target+error-403})
    require(len(fallbacks) == 8 and len(cores) == 2 and F(old['positive_denominator_lower_factor']) > 0
            and F(src['old_mass_coefficient'])-F(23, 42)*h > 0,
            'All fallback branches, terminal quantities and positive division remain')
    critical_R = (h*mass(s0)-escape(s0))/(A-h)
    require(0 < critical_R < R1 and escape(s1)-h*mass(s1) > 0,
            'The new rectangle is wide enough in both source and residual coordinates')
    improvement = F(old['candidate_K'])-target
    require(improvement > 0, 'A strict complete global improvement over163')
    return encode({'schema': 'erdos7-union-source-outer-comparison-v1', 'source_sha256': pins,
                   'old_source_radius': s0, 'old_residual_radius': R0, 'old_slot_radius': r0,
                   'new_source_radius': s1, 'new_residual_radius': R1, 'new_slot_radius': par['rbar'],
                   'old_complement_residual_floor': floor, 'original_outer_slot_cutoff': rcut,
                   'old_K0': K0, 'decrement_from_K0': h, 'candidate_K': target,
                   'previous163_K': F(old['candidate_K']), 'improvement_over163': improvement,
                   'marked_residual_coefficient': A-h-P-L5, 'unmarked_residual_coefficient': A-h,
                   'bridge_critical_residual_radius': critical_R,
                   'original_fixed_outer_cost_count': old['original_fixed_outer_cost_count'],
                   'complete_outer_endpoints': rows, 'controlling_branches': controlling,
                   'local_complete_bounds': local_rows, 'fallbacks': fallbacks, 'complete_cores': cores,
                   'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
                   'scope': 'Ordinary full-domain comparison joining two complete local source domains. Every local bound is used on its own source only. Eleven outside endpoints, all eight original fallbacks, both complete terminal errors and infinite tails remain. One actual residual with r<=5rho. No canonical118 mutation, Lean claim or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('union_source_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete global union certificate')
    print('PASS: two complete source domains plus their complement; K<='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
