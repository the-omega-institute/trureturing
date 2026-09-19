#!/usr/bin/env python3
"""Remove the slot-cutoff complement using two complete larger source domains."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/full_slot_union_outer_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/union_source_outer_comparison.py': 'b068d801b27cdfac197f294f170fe861847177ef88db7d98182c4efc2e5891d2', 'certificates/source_norms/union_source_outer_comparison.json': 'e00e1276338a35002a606adcf7b05124eb59afdd3936e32ec71efe83a6be99cc', 'frontier/full_slot_source_transport.py': '0cdab1b10304b24280cbab675a5a355b6676e9010762146131930f4e688734d9', 'certificates/source_norms/full_slot_source_transport.json': '2a3afcd19b14a6edabaf6b3c6dd415db11469e2b35281bd9cce30685941975da', 'frontier/transported_source_complete_comparison.py': 'f1ae240968de56400d9a49b5220c05291b744d4557fbdd939daec58dda587a4c', 'certificates/source_norms/transported_source_complete_comparison.json': 'b184a3b2ef13033a99df580b5ea081e0251e14c4cfd9ba482ebeb847a7c17200'}


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
    require(PINS, 'Both complete larger-domain results must be pinned before consumption')
    io = module('union_source_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    inputs = {name: read(name) for name in ('union_source_outer_comparison', 'full_slot_source_transport',
                                         'transported_source_complete_comparison')}
    pins = dict(PINS)
    for entry in inputs.values():
        for path, pin in entry['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original source closure '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    old = module('union_source_old', base/'frontier/union_source_outer_comparison.py').calculate(base)
    require(old == inputs['union_source_outer_comparison'], 'Reconstruct the preceding full global partition')
    local = inputs['full_slot_source_transport']
    expanded = inputs['transported_source_complete_comparison']
    p0 = {key: F(local['parameters'][key]) for key in ('delta', 'rho', 'rbar')}
    p1 = {key: F(expanded['parameters'][key]) for key in ('delta', 'rho', 'rbar')}
    s0, R0, s1, R1 = p0['delta'], p0['rho'], p1['delta'], p1['rho']
    require((s0, R0, p0['rbar']) == (F(1, 26), F(1, 1000), F(1, 200))
            and (s1, R1, p1['rbar']) == (F(1, 18), F(1, 13000), F(1, 2600)),
            'Two complete domains with actual r<=5rho and no independent cutoff')
    require(0 < R1 < R0 and s0 < s1 < F(1, 3), 'The overlapping complete source rectangles')
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
    require(s0 < F(old_outer['delta']) and rcut == F(old_outer['slot_cutoff'])
            and limit == F(old_outer['signed_mass_limit']) and slope == F(old_outer['signed_mass_slope']),
            'The entire marked region is inside its original proved domain')
    escape = lambda s: gamma2*s-(gamma2-gamma1)*s*s
    marked = lambda s: B0-B1*s+B2*s*s-Q*s+escape(s)
    mass = lambda s, u=F(0): a+slope*s+u
    floor = R0
    require(p0['rbar'] == 5*R0 and p1['rbar'] == 5*R1,
            'Both complete local bounds cover every actual slot loss in their residual rectangle')
    rows = []

    def endpoint(branch, sigma, reserve, payment, residual_lower=F(0)):
        require(reserve > 0 and payment > 0, 'Positive full endpoint quantities')
        rows.append({'branch': branch, 'sigma': sigma, 'residual_lower': residual_lower,
                     'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                     'decrement_capacity': reserve/payment})

    for s, tag in ((F(0), 'zero'), (s0, 'old_source_radius')):
        endpoint('low_source_marked_'+tag, s, marked(s)+(A-P-L5)*floor, mass(s, floor), floor)
    large_floor = max(floor, rcut/5)
    endpoint('low_source_large_r', s0, A*large_floor, mass(s0, large_floor), large_floor)
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
    require(controlling == ['low_source_marked_zero'], 'The residual boundary controls after removal of the old independent slot cutoff')
    for row in rows:
        row['margin'] = row['reserve_at_K0']-h*row['target_payment_coefficient']
    require(sum(r['margin'] == 0 for r in rows) == 1 and all(r['margin'] >= 0 for r in rows),
            'Every entire interval has its required nonnegative endpoints')
    require(gamma2-gamma1-B2 > 0 and gamma2-gamma1-F(11, 36)*h > 0
            and A-h-P-L5 > 0 and A-h > 0, 'Concavity and one common residual justify all reductions')
    target = K0-h
    local_rows = []
    for label, result, par in (('full_slot_source_transport', local, p0),
                               ('transported_source_complete_comparison', expanded, p1)):
        bound = result['comparison']
        upper = F(bound['comparison_upper'])
        require(bound['all_original_indices'] == list(range(52))
                and F(bound['remaining_S_coefficient']) > 0
                and F(bound['denominator_at_mass_floor']) > 0 and upper < target,
                'The complete original52 comparison and actual mass hold on their own full rectangle')
        local_rows.append({'source': label, 'rho_lower': F(0), 'rho_upper': par['rho'],
                           'source_radius': par['delta'], 'implied_slot_radius': par['rbar'],
                           'complete_bound': upper})
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
    require(improvement > 0, 'A strict complete global improvement over167')
    return encode({'schema': 'erdos7-full-slot-union-outer-comparison-v1', 'source_sha256': pins,
                   'low_source_radius': s0, 'low_residual_radius': R0, 'low_implied_slot_radius': p0['rbar'],
                   'wide_source_radius': s1, 'wide_residual_radius': R1, 'wide_implied_slot_radius': p1['rbar'],
                   'low_complement_residual_floor': floor, 'original_outer_slot_cutoff': rcut,
                   'old_K0': K0, 'decrement_from_K0': h, 'candidate_K': target,
                   'previous167_K': F(old['candidate_K']), 'improvement_over167': improvement,
                   'marked_residual_coefficient': A-h-P-L5, 'unmarked_residual_coefficient': A-h,
                   'bridge_critical_residual_radius': critical_R,
                   'original_fixed_outer_cost_count': old['original_fixed_outer_cost_count'],
                   'complete_outer_endpoints': rows, 'controlling_branches': controlling,
                   'local_complete_bounds': local_rows, 'fallbacks': fallbacks, 'complete_cores': cores,
                   'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
                   'scope': 'Ordinary full-domain comparison joining173 and170 complete source domains without an independent local slot cutoff. Every local bound is used on its own source only. Eleven outside endpoints, all eight original fallbacks, both complete terminal errors and infinite tails remain. One actual residual with r<=5rho. No canonical118 mutation, Lean claim or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('union_source_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete full-slot global union certificate')
    print('PASS: two complete source domains plus their complement; K<='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
