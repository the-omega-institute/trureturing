#!/usr/bin/env python3
"""Join the complete2/27 source rectangle with both three-layer alternatives."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/next_wide_source_union.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/three_layer_global_comparison.py': 'f38a892b67c66102e4ca76ec4421cb1b4a724452b790420a8508c67bf87b0185', 'certificates/source_norms/three_layer_global_comparison.json': '0600b85a3c3fa1a766289084240fc919a962ad49bc1787558cfedfe2fe23b5a9', 'frontier/three_layer_product_escape.py': '103e3ccef4faf50c2c326ce74ad4ddf9831f4d6adf27af106491ba2d20099baa', 'certificates/source_norms/three_layer_product_escape.json': '32bdd5c948dda2e3757513e8c7c42d62bd5da0ea2dd321a101675bd13a8716fc', 'frontier/wide_source_bridge_comparison.py': '67e211253fd67117fd694f2cf7989dbec6fef8252a68fd0c5d31662d9de67705', 'certificates/source_norms/wide_source_bridge_comparison.json': '3570969e256dc36764e050fc2814466380d68510ada31ad6b59f6f6515d008da', 'frontier/wide_fresh_full_slot_source_comparison.py': '8b92c7eda87c06ca763d50015b5dd6078730cdb3c7af81aa8a46c989ba3f425d', 'certificates/source_norms/wide_fresh_full_slot_source_comparison.json': '7e8ba6cbd1fa404bf9274cd32e102fa40bf9b7bc7c4ad4c46c2b42b71a61a71a'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original proof input')
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
    require(PINS, 'Pin both complete local domains and the three-layer source theorem')
    io = module('next_wide_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    old, joint = read('three_layer_global_comparison'), read('three_layer_product_escape')
    local_inputs = {name: read(name) for name in
        ('wide_fresh_full_slot_source_comparison', 'wide_source_bridge_comparison')}
    pins = dict(PINS)
    for data in (old, joint, *local_inputs.values()):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    local = local_inputs['wide_fresh_full_slot_source_comparison']
    wide = local_inputs['wide_source_bridge_comparison']
    p0, p1 = ({k: F(data['parameters'][k]) for k in ('delta', 'rho', 'rbar')} for data in (local, wide))
    s0, R0, s1, R1 = p0['delta'], p0['rho'], p1['delta'], p1['rho']
    require((s0, R0, p0['rbar']) == (F(1, 20), F(1, 1000), F(1, 200))
            and (s1, R1, p1['rbar']) == (F(2, 27), F(1, 13000), F(1, 2600))
            and p0['rbar'] == 5*R0 and p1['rbar'] == 5*R1,
            'Both complete rectangles include every actual slot loss allowed by r<=5rho')
    A, q, K0, H, eK, eJ, eB, eC, g1, g2, g3 = (F(joint[k]) for k in (
        'signed_mass_coefficient', 'survival_mass_coefficient', 'old_K0', 'decrement_capacity',
        'K_denominator_payment', 'J_denominator_payment', 'next_denominator_payment',
        'third_denominator_payment', 'first_escape_gap', 'next_escape_gap', 'third_escape_gap'))
    require(K0 == F(old['old_K0']) and q == F(23, 42)
            and 0 < s0 < s1 < 1 and 0 < R1 < R0 and 0 < eK < eB < eJ < eC,
            'The same original source target and the ordered paired layers')
    scale, endpoints = 10**30, []
    intervals = (('low', F(0), s0, R0), ('bridge', s0, s1, R1), ('outer', s1, F(1), F(0)))
    for branch, left, right, R in intervals:
        for side, sigma in (('left', left), ('right', right)):
            x = 1-sigma
            n = isqrt(x.numerator*scale*scale//x.denominator)
            lo, hi = F(n, scale), F(n+1, scale)
            require(0 <= lo <= 1 and lo*lo <= x < hi*hi, 'Exact rational square-root bracket')
            jcap = (1-lo)**2
            pairs = (('next', g2*sigma+A*R, eK+(eB-eK)*sigma+q*R),
                     ('J', g3*sigma-(g3-g1)*jcap+A*R,
                      eK+(eC-eK)*sigma+(eJ-eC)*jcap+q*R))
            for alternative, reserve, payment in pairs:
                require(0 <= jcap <= sigma*sigma and reserve > 0 and payment > 0,
                        'A positive paired endpoint, without an independent payment bound')
                endpoints.append({'branch': branch+'_'+side, 'alternative': alternative,
                    'sigma': sigma, 'residual_lower': R, 'sqrt_lower': lo, 'sqrt_upper': hi,
                    'J_mass_upper': jcap, 'reserve_at_K0': reserve,
                    'target_payment_coefficient': payment, 'decrement_capacity': reserve/payment})
    require(len(endpoints) == 12, 'Both alternatives at both endpoints of the entire three-region complement')
    h = min(r['decrement_capacity'] for r in endpoints)
    controllers = [(r['branch'], r['alternative']) for r in endpoints if r['decrement_capacity'] == h]
    require(controllers == [('bridge_left', 'next')] and F(old['decrement_from_K0']) < h < H,
            'The lower source junction now uniquely controls, with a strict complete improvement')
    j_coefficient = g1-g3-h*(eJ-eC)
    j_quadratic = g1-2*g3-h*(eK+eJ-2*eC)
    next_quadratic = -g2+h*(eB-eK)
    require(j_coefficient < 0 and j_quadratic < 0 and next_quadratic < 0
            and A-q*h > 0 and K0-F(joint['old_offset'])-h > 0,
            'Correct joint J-mass substitution, both concavities and original true-function coefficient signs')
    for row in endpoints:
        row['certified_margin'] = row['reserve_at_K0']-h*row['target_payment_coefficient']
        require(row['certified_margin'] >= 0, 'Every true algebraic endpoint has a nonnegative rational lower margin')
    require(sum(r['certified_margin'] == 0 for r in endpoints) == 1, 'The controlling endpoint is unique')
    target, local_rows = K0-h, []
    for name, data in local_inputs.items():
        c, heads, par = data['comparison'], data['complete_heads'], data['parameters']
        indices = ([r['index'] for r in heads['mean_costs']+heads['quadratic_costs']+c['simple_costs']]
                   +[0, 16, 46, 47])
        bound, denominator, numerator, offset = (F(c[k]) for k in
            ('comparison_upper', 'denominator_at_mass_floor', 'signed_endpoint', 'offset'))
        require(sorted(indices) == c['all_original_indices'] == list(range(52))
                and denominator > 0 and F(c['remaining_S_coefficient']) > 0
                and bound == offset+numerator/denominator < target
                and F(par['rbar']) == 5*F(par['rho']),
                'Every complete independent local cost, actual-mass coefficient and positive denominator remains')
        local_rows.append({'source': name, 'source_radius': F(par['delta']),
            'residual_radius': F(par['rho']), 'implied_slot_radius': F(par['rbar']),
            'complete_bound': bound, 'candidate_target_margin': target-bound})
    fallbacks = [{'branch': row['branch'], 'complete_bound': F(row['complete_bound']),
                  'candidate_target_gap': target-F(row['complete_bound'])} for row in old['fallbacks']]
    cores = [{'box': row['box'], 'unchanged_error': F(row['unchanged_error']),
              'candidate_complete_gap': target+F(row['unchanged_error'])-403} for row in old['complete_cores']]
    require(len(fallbacks) == 8 and min(row['candidate_target_gap'] for row in fallbacks) > 0
            and len(cores) == 2 and min(row['candidate_complete_gap'] for row in cores) > 0
            and F(old['positive_denominator_lower_factor']) > 0,
            'All original fallback branches and full terminal errors remain; unrestricted problem unresolved')
    return encode({'schema': 'erdos7-next-wide-source-union-v1', 'source_sha256': pins,
        'low_source_radius': s0, 'low_residual_radius': R0,
        'wide_source_radius': s1, 'wide_residual_radius': R1,
        'old_K0': K0, 'previous193_K': F(old['candidate_K']), 'candidate_K': target,
        'decrement_from_K0': h, 'improvement_over193': F(old['candidate_K'])-target,
        'proved_decrement_limit': H, 'square_root_bracket_denominator': scale,
        'complete_outer_endpoints': endpoints, 'controlling_branches': controllers,
        'joint_J_coefficient': j_coefficient, 'J_square_root_quadratic_coefficient': j_quadratic,
        'next_square_root_quadratic_coefficient': next_quadratic,
        'remaining_mass_coefficient': A-q*h, 'local_complete_bounds': local_rows,
        'fallbacks': fallbacks, 'complete_cores': cores,
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'scope': 'Ordinary complete global comparison joining181 and188 full actual-source rectangles. Their entire complement uses192 paired beta-product alternatives with one actual residual; both alternatives are concave in sqrt(1-sigma). All12 endpoints, every original52 local cost, full local denominators, eight fallbacks and two terminal errors remain. No new moment theorem, actual-family attainment, Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('next_wide_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact next-layer wider complete source union')
    print('PASS:181+188 complete source union and all12 paired endpoints; global K='
          +str(float(F(result['candidate_K'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
