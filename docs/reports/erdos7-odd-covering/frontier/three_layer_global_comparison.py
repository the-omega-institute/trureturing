#!/usr/bin/env python3
"""Join the complete source union using both beta-separated escape alternatives."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/three_layer_global_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/square_root_product_escape_comparison.py': 'edc2c8ccc995cd4931a8599fa4ae51a1c4f437c8fb9c61917b3b85a1cb18a6ba', 'certificates/source_norms/square_root_product_escape_comparison.json': '068c3249b73afcc47d9c6afe774f8767a172461e8a18b867fdd138ec9f478905', 'frontier/three_layer_product_escape.py': '103e3ccef4faf50c2c326ce74ad4ddf9831f4d6adf27af106491ba2d20099baa', 'certificates/source_norms/three_layer_product_escape.json': '32bdd5c948dda2e3757513e8c7c42d62bd5da0ea2dd321a101675bd13a8716fc'}


def require(test, message):
    if not test:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned logical reader')
    io = module('sqrt_escape_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    old, joint, product = (read(n) for n in ('square_root_product_escape_comparison',
                                          'three_layer_product_escape', 'k_next_escape_layers'))
    pins = dict(PINS)
    for data in (old, joint, product):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original proof source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    require('sqrt(qK)+sqrt(qJ) <= 1' in product['product_mass_constraints'], 'Original stronger product inequality')
    A, q, g1, g2, K0, H, eK, eJ, eB = (F(joint[k]) for k in (
        'signed_mass_coefficient', 'survival_mass_coefficient', 'first_escape_gap', 'next_escape_gap',
        'old_K0', 'decrement_capacity', 'K_denominator_payment', 'J_denominator_payment', 'next_denominator_payment'))
    require(q == F(23, 42) and eK < eB < eJ and K0 == F(old['old_K0']), 'Same original joint layer theorem')
    g3, eC = F(joint['third_escape_gap']), F(joint['third_denominator_payment'])
    scale, endpoints = 10**30, []
    for previous in old['complete_outer_endpoints']:
        sigma, R = F(previous['sigma']), F(previous['residual_lower'])
        value = 1-sigma
        n = isqrt(value.numerator*scale**2//value.denominator)
        lo, hi = F(n, scale), F(n+1, scale)
        require(0 <= lo <= 1 and lo*lo <= value < hi*hi, 'Exact rational square-root enclosure')
        jcap = (1-lo)**2
        pairs = (
            ('next', g2*sigma+A*R, eK+(eB-eK)*sigma+q*R),
            ('J', g3*sigma-(g3-g1)*jcap+A*R, eK+(eC-eK)*sigma+(eJ-eC)*jcap+q*R))
        for alternative, reserve, payment in pairs:
            require(0 <= jcap <= sigma*sigma and reserve > 0 and payment > 0,
                    'Safe paired reserve and payment for both alternatives')
            endpoints.append({'branch': previous['branch'], 'alternative': alternative,
                              'sigma': sigma, 'residual_lower': R,
                              'sqrt_lower': lo, 'sqrt_upper': hi, 'J_mass_upper': jcap,
                              'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                              'decrement_capacity': reserve/payment})
    require([(r['sigma'], r['residual_lower']) for r in endpoints[::2]] == [
        (F(0), F(1, 1000)), (F(1, 20), F(1, 1000)), (F(1, 20), F(1, 13000)),
        (F(1, 18), F(1, 13000)), (F(1, 18), F(0)), (F(1), F(0))], 'Complete inherited three-region complement')
    h = min(r['decrement_capacity'] for r in endpoints)
    controllers = [(r['branch'], r['alternative']) for r in endpoints if r['decrement_capacity'] == h]
    require(controllers == [('outer_wide_radius', 'next')] and 0 < F(old['decrement_from_K0']) < h < H,
            'Strict complete gain within the existing joint-layer interval')
    t_quadratic = g1-2*g3-h*(eK+eJ-2*eC)
    require(t_quadratic < 0 and g1-g3-h*(eJ-eC) < 0 and -g2+h*(eB-eK) < 0 and A-q*h > 0
            and K0-F(joint['old_offset'])-h > 0, 'Concavity in square-root coordinate and all original coefficient signs')
    for row in endpoints:
        row['certified_margin'] = row['reserve_at_K0']-h*row['target_payment_coefficient']
        require(row['certified_margin'] >= 0, 'Every true algebraic endpoint has a nonnegative rational lower margin')
    target = K0-h
    local = old['local_complete_bounds']
    require(len(local) == 2 and all(F(r['complete_bound']) < target for r in local), 'Both full52 local comparisons remain below target')
    for row in local:
        data = read(row['source']); c = data['comparison']
        require(c['all_original_indices'] == list(range(52)) and F(c['denominator_at_mass_floor']) > 0
                and F(c['remaining_S_coefficient']) > 0 and F(c['comparison_upper']) == F(row['complete_bound'])
                and F(row['implied_slot_radius']) == 5*F(row['residual_radius']), 'Complete local costs, positive division and actual slot domain')
    fallbacks = [{'branch': r['branch'], 'complete_bound': F(r['complete_bound']),
                  'candidate_target_gap': target-F(r['complete_bound'])} for r in old['fallbacks']]
    cores = [{'box': r['box'], 'unchanged_error': F(r['unchanged_error']),
              'candidate_complete_gap': target+F(r['unchanged_error'])-403} for r in old['complete_cores']]
    require(len(fallbacks) == 8 and min(r['candidate_target_gap'] for r in fallbacks) > 0
            and len(cores) == 2 and min(r['candidate_complete_gap'] for r in cores) > 0
            and F(old['positive_denominator_lower_factor']) > 0, 'All complete fallbacks and terminal errors remain; problem unresolved')
    eta = g3-H*eC
    threshold_t = 2*eta/(2*eta+H*eK)
    J_threshold = 1-threshold_t*threshold_t
    next_threshold = H*eK/(g2-H*(eB-eK))
    threshold_sigma = max(J_threshold, next_threshold)
    require(0 < J_threshold < next_threshold < F(old['full_capacity_threshold_sigma']) < 1,
            'Both exact auxiliary alternatives lower the full-capacity source transition')
    encode = module('sqrt_escape_encode', base/'frontier/joint_gap_mass_escape.py').encode
    return encode({'schema': 'erdos7-three-layer-global-comparison-v1', 'source_sha256': pins,
        'old_K0': K0, 'previous190_K': F(old['candidate_K']), 'candidate_K': target,
        'decrement_from_K0': h, 'improvement_over190': F(old['candidate_K'])-target,
        'proved_decrement_limit': H, 'square_root_bracket_denominator': scale,
        'complete_outer_endpoints': endpoints, 'controlling_branches': controllers,
        'square_root_coordinate_quadratic_coefficient': t_quadratic,
        'remaining_mass_coefficient': A-q*h,
        'local_complete_bounds': local, 'fallbacks': fallbacks, 'complete_cores': cores,
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'full_capacity_J_threshold_t': threshold_t, 'full_capacity_J_threshold_sigma': J_threshold,
        'full_capacity_next_threshold_sigma': next_threshold, 'full_capacity_threshold_sigma': threshold_sigma,
        'scope': 'Ordinary complete global comparison retaining the common beta factor of the J and next source layers. Both auxiliary alternatives are concave in sqrt(1-sigma); all twelve endpoint margins are checked. Rational square-root brackets are used only for the J alternative; the controlling next-layer endpoint is exactly rational. All52 local costs, eight fallbacks, both full terminal errors and independent labels/tails remain. No actual-family attainment, Lean verification or Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true'); mode.add_argument('--check', action='store_true')
    args = parser.parse_args(); result = calculate(args.base)
    io = module('sqrt_escape_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete beta-separated source certificate')
    print('PASS: beta-separated alternatives, twelve exact endpoint margins and full comparison; K='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr); sys.exit(1)
