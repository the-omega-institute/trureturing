#!/usr/bin/env python3
"""Keep the original square-root product exclusion in the complete source union."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/square_root_product_escape_comparison.json'
PINS = {'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232', 'frontier/joint_gap_denominator_global_comparison.py': 'c3813624a5d90cca7906a731c0611c96bd3af4dae88948e504204e74632ac6a4', 'certificates/source_norms/joint_gap_denominator_global_comparison.json': 'c05af69fcd7c49d142319cda0f93f6a8426f9eddefd15f46ef0c30244ba1bda7', 'frontier/joint_gap_denominator_escape.py': 'fd1febb46588bc7ffb9472e4741dcb3aae4a5411a3a9331afef7947b387f12de', 'certificates/source_norms/joint_gap_denominator_escape.json': '1da26e786818cc6f2c4c89d04cc100fc1dea4637a3fe5554e4224c0807749fae', 'frontier/k_next_escape_layers.py': 'f17140e366688960a1dcd04e3c72287c9acbeace1c865f0d1905a0d8d051a5b1', 'certificates/source_norms/k_next_escape_layers.json': '68e181fcd4bb06953a03688260c8d426ee34c607bc73a5b5b8e49ee94fab00a8', 'profile-notes/92-the-next-k-escape-layers-and-product-exclusion.md': '46f8480e279af288253d71b2f36497ede91ae9443741b772697b58c1109ce96e'}


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
    old, joint, product = (read(n) for n in ('joint_gap_denominator_global_comparison',
                                          'joint_gap_denominator_escape', 'k_next_escape_layers'))
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
    scale, endpoints = 10**30, []
    for previous in old['complete_outer_endpoints']:
        sigma, R = F(previous['sigma']), F(previous['residual_lower'])
        value = 1-sigma
        n = isqrt(value.numerator*scale**2//value.denominator)
        lo, hi = F(n, scale), F(n+1, scale)
        require(0 <= lo <= 1 and lo*lo <= value < hi*hi, 'Exact rational square-root enclosure')
        jcap = (1-lo)**2
        reserve = g2*sigma-(g2-g1)*jcap+A*R
        payment = eK+(eB-eK)*sigma+(eJ-eB)*jcap+q*R
        require(0 <= jcap <= sigma*sigma and reserve > 0 and payment > 0, 'Sharper safe endpoint J cap')
        endpoints.append({'branch': previous['branch'], 'sigma': sigma, 'residual_lower': R,
                          'sqrt_lower': lo, 'sqrt_upper': hi, 'J_mass_upper': jcap,
                          'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                          'decrement_capacity': reserve/payment})
    require([(r['sigma'], r['residual_lower']) for r in endpoints] == [
        (F(0), F(1, 1000)), (F(1, 20), F(1, 1000)), (F(1, 20), F(1, 13000)),
        (F(1, 18), F(1, 13000)), (F(1, 18), F(0)), (F(1), F(0))], 'Complete inherited three-region complement')
    h = min(r['decrement_capacity'] for r in endpoints)
    controllers = [r['branch'] for r in endpoints if r['decrement_capacity'] == h]
    require(controllers == ['outer_wide_radius'] and 0 < F(old['decrement_from_K0']) < h < H,
            'Strict complete gain within the existing joint-layer interval')
    t_quadratic = g1-2*g2-h*(eK+eJ-2*eB)
    require(t_quadratic < 0 and g1-g2-h*(eJ-eB) < 0 and A-q*h > 0
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
    eta = g2-H*eB
    threshold_t = 2*eta/(2*eta+H*eK)
    threshold_sigma = 1-threshold_t*threshold_t
    require(0 < threshold_sigma < F(joint['capacity_lower_root']) < 1,
            'The exact stronger product constraint lowers the full-capacity source transition')
    encode = module('sqrt_escape_encode', base/'frontier/joint_gap_mass_escape.py').encode
    return encode({'schema': 'erdos7-square-root-product-escape-comparison-v1', 'source_sha256': pins,
        'old_K0': K0, 'previous187_K': F(old['candidate_K']), 'candidate_K': target,
        'decrement_from_K0': h, 'improvement_over187': F(old['candidate_K'])-target,
        'proved_decrement_limit': H, 'square_root_bracket_denominator': scale,
        'complete_outer_endpoints': endpoints, 'controlling_branches': controllers,
        'square_root_coordinate_quadratic_coefficient': t_quadratic,
        'remaining_mass_coefficient': A-q*h,
        'local_complete_bounds': local, 'fallbacks': fallbacks, 'complete_cores': cores,
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'full_capacity_threshold_t': threshold_t, 'full_capacity_threshold_sigma': threshold_sigma,
        'scope': 'Ordinary complete global comparison with the original sqrt(qK)+sqrt(qJ)<=1 product constraint retained. Concavity is proved in t=sqrt(1-sigma), not assumed in sigma. Exact rational brackets bound the true algebraic endpoint margins. All52 local costs, eight fallbacks, both full terminal errors and independent labels/tails remain. No exact algebraic optimum, actual attainment, Lean verification or Erdos7 resolution.'})


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
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact stronger-product complete certificate')
    print('PASS: square-root product exclusion, six exact endpoint enclosures and full comparison; K='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr); sys.exit(1)
