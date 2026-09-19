#!/usr/bin/env python3
"""Join the aggregate K/next-layer exclusion to the complete J reserve."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from math import isqrt
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/j_aggregate_layer_global_comparison.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/j_family_global_comparison.py': '068c3623c6e0d627ad7247fec99d5aa7a28c9e019dc54c0b6d668d5f4e040259',
    'certificates/source_norms/j_family_global_comparison.json': 'ebb4068b2b4bdb24694469480a9665b717dc8be84f00be35553aa45d03d32b7a',
    'frontier/three_layer_product_escape.py': '103e3ccef4faf50c2c326ce74ad4ddf9831f4d6adf27af106491ba2d20099baa',
    'certificates/source_norms/three_layer_product_escape.json': '32bdd5c948dda2e3757513e8c7c42d62bd5da0ea2dd321a101675bd13a8716fc',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
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
    require(PINS and sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned logical reader and completed proof inputs')
    io = module('actual_j_io', base/'certificate_io.py')
    read = lambda n: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(n+'.json')))
    old, joint, jface, jnear, wide, low, family = (read(n) for n in (
        'j_family_global_comparison', 'three_layer_product_escape', 'j_face_alignment',
        'j_source_labelwise_neighborhood', 'extended_source_bridge_comparison',
        'wide_fresh_full_slot_source_comparison', 'j_family_error_reserve'))
    pins = dict(PINS)
    for data in (old, joint, jface, jnear, wide, low, family):
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent original input '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned logical input '+path)
    load = lambda n: module('actual_j_'+n, base/'frontier'/(n+'.py'))
    A, q, K0, H, g1, g2, eK, eJ, eB = (F(joint[k]) for k in (
        'signed_mass_coefficient', 'survival_mass_coefficient', 'old_K0', 'decrement_capacity',
        'first_escape_gap', 'next_escape_gap', 'K_denominator_payment',
        'J_denominator_payment', 'next_denominator_payment'))
    g3, eC = F(joint['third_escape_gap']), F(joint['third_denominator_payment'])
    d, R = F(1, 2500), F(1, 100000)
    t0 = d/2
    far_reserve = -H*eK*t0*t0+2*(g3-H*eC)*t0*(1-t0)
    far_payment = eK*t0*t0+eJ*(1-t0)**2+2*eC*t0*(1-t0)
    require(far_reserve > 0 and far_payment > 0 and t0 == F(1, 5000),
            'Positive true four-layer J-alternative reserve and its own target payment')
    extra = far_reserve/far_payment
    require(extra > F(old['extra_decrement']), 'The aggregate exclusion improves the same complete J neighborhood')
    h = H+extra
    target = K0-h
    require(q == F(23, 42) and H == g1/eJ and h > H and A-q*h > 0
            and K0-F(joint['old_offset'])-h > 0, 'A new target past the original J capacity, with positive true coefficients')

    # Extend the old paired layers by reconstructing the actual53 allocation.
    # No extension is inferred from the previous H-limited wrapper.
    source = module('actual_j_source', base/'verify_joint_frontier.py')
    allocated, control = load('allocated_seven_thresholds'), load('global_control_faces')
    old53, faces, survival, dictionary = (read(n) for n in (
        'allocated_seven_thresholds', 'global_control_faces', 'joint_survival_carriers', 'k_signed_gap_dictionary'))
    metadata = []
    for i, vertex in enumerate(source.vertices()):
        dat = source.data(vertex)
        metadata.append({'index': i, 's': dat[3], 'D': dat[4]})
    rows, stats = allocated.reconstruct(source, survival, metadata)
    require(encode(stats) == old53['allocation_statistics'] and len(rows) == 1296,
            'Fresh original allocated margins and their complete conditional digest')
    Kset = {(r['index'], r['carrier_index']) for r in faces['targets']['K']['zero_controls']}
    Jset = {(r['index'], r['carrier_index']) for r in faces['targets']['J']['zero_controls']}
    require(len(Kset) == 6 and len(Jset) == 18 and not Kset & Jset, 'Original disjoint K/J control sets')
    layer_data = read('k_next_escape_layers')
    Bset = {(r['index'], r['carrier_index']) for r in layer_data['next_layer_controls']}
    require(Bset == {(386, 14), (592, 13)} and not Bset & (Kset | Jset),
            'The original two next controls, disjoint from K and J')
    values, lookup = list(map(F, dictionary['rational_values'])), dictionary['lower_gap_value_indices']
    original, lower, payments = [], [], []
    for i, row in enumerate(rows):
        require(row['index'] == i and len(row['conditional']) == 18, 'Every original carrier row')
        for j, cond in enumerate(row['conditional']):
            require(tuple(cond['carrier']) == allocated.CARRIERS[j] == tuple(faces['carriers'][j]),
                    'Original source and carrier ordering')
            dc, margin, raw = cond['D_c'], cond['M'], row['s']
            gap = values[lookup[18*i+j]]
            payment = q*dc+margin
            require(0 < payment <= dc <= raw, 'Actual original lower denominator and survivor interval')
            original.extend(((i, j, 'D_c', gap), (i, j, 's', gap+A*(raw-dc))))
            lower.append((i, j, dc, raw, gap, payment))
            payments.append((i, j, dc, margin, payment))
    require(control.digest(original) == joint['complete_original_endpoint_table_sha256']
            and control.digest(payments) == joint['same_source_denominator_table_sha256'],
            'Every original gap remains paired with the same allocated denominator')
    layer_checks = []
    for decrement in (F(0), h):
        floors = (-decrement*eK, g1-decrement*eJ, g2-decrement*eB, g3-decrement*eC)
        slacks, outside_controls = [], []
        for i, j, dc, raw, gap, payment in lower:
            layer = 0 if (i, j) in Kset else 1 if (i, j) in Jset else 2 if (i, j) in Bset else 3
            slack = gap-decrement*payment-floors[layer]
            require(slack >= 0 and slack+(A-q*decrement)*(raw-dc) >= 0,
                    'Both mass endpoints of every paired row hold beyond H')
            slacks.append(slack)
            if layer == 3 and slack == 0:
                outside_controls.append((i, j))
        require(outside_controls == [(386, 15), (386, 16), (386, 17), (592, 15), (592, 16), (592, 17)],
                'The same six exact fourth-layer controls after extension')
        layer_checks.append({'decrement': decrement, 'floors': floors,
                             'lower_checks': len(lower), 'upper_checks': len(lower),
                             'minimum_slack': min(slacks), 'outside_controllers': outside_controls})
    fK, fJ, fB, fC = -h*eK, g1-h*eJ, g2-h*eB, g3-h*eC
    a, u, v = fJ-fK, fC-fB, fC-fJ
    require(fK < fJ < 0 < fB < fC and a > 0 and u > 0 and v > 0,
            'The negative J floor and all positive aggregate exclusion coefficients')
    Anew = A-q*h

    # The full local domains, not just isolated parameter points.
    require(tuple(F(low['parameters'][k]) for k in ('delta', 'rho', 'rbar'))
            == (F(1, 20), F(1, 1000), F(1, 200))
            and tuple(F(wide['parameters'][k]) for k in ('delta', 'rho', 'rbar'))
            == (F(1, 12), F(1, 3000), F(1, 600)), 'Both complete actual source rectangles')
    scale = 10**30

    def bracket(x):
        n = isqrt(x.numerator*scale*scale//x.denominator)
        lo, hi = F(n, scale), F(n+1, scale)
        require(lo*lo <= x < hi*hi and 0 <= lo <= 1, 'Integer-certified square-root enclosure')
        return lo, hi

    inner_endpoints = []
    for branch, left, right, residual in (
            ('low_outer', F(0), F(1, 20), F(1, 1000)),
            ('bridge_outer', F(1, 20), F(1, 12), F(1, 3000))):
        for side, sigma in (('left', left), ('right', right)):
            lo, hi = bracket(1-sigma)
            jcap = (1-lo)**2
            for name, gap in (
                    ('B', fK*(1-sigma)+fB*sigma+Anew*residual),
                    ('J', fK*(1-sigma)+fC*sigma+(fJ-fC)*jcap+Anew*residual)):
                require(gap > 0, 'Both aggregate alternatives pass every full inner endpoint')
                inner_endpoints.append({'branch': branch+'_'+side, 'alternative': name,
                                        'sigma': sigma, 'residual_lower': residual,
                                        'sqrt_lower': lo, 'sqrt_upper': hi, 'margin_lower': gap})
    require(fK-fB < 0 and fK+fJ-2*fC < 0 and fJ-fC < 0,
            'Both complete alternatives are concave with correct signed root substitution')

    # The outer region has x=qK<=11/12. Split at y=qJ=1-d.
    cap = F(11, 12)
    require(0 < d*d < cap and d+R < F(1, 1000), 'Exact J neighborhood inside the ordinary136 theorem domain')
    require(t0*t0 < cap and (1-t0)**2 >= 1-d,
            'The exact J-complement transition1-sqrt(1-d) is at least d/2')
    far_B = fK*cap+fB*(1-cap)
    far_J_start = fK*t0*t0+fJ*(1-t0)**2+2*fC*t0*(1-t0)
    lo, hi = bracket(cap)
    far_J_end = fK*cap+fC*(1-cap)+(fJ-fC)*(1-lo)**2
    require(far_B > 0 and far_J_start == 0 and far_J_end > 0 and u+v > 0,
            'The aggregate far-J region passes all three complete concave endpoints')
    near_high = fJ-a*d*d+Anew*R
    require(near_high > 0, 'The same actual residual pays the entire negative J floor above R')
    jprovider = load('j_family_error_reserve')
    require(jprovider.calculate(base) == family, 'Reconstruct the complete197 family theorem and all its original source guards')
    family_bound = jprovider.reserve_bound(d, R)
    require(jprovider.encode(family_bound) == {k: v for k, v in next(
        r for r in family['complete_rectangles'] if F(r['source_radius']) == d and F(r['residual_radius']) == R).items()
        if k not in ('predecessor_complete_error', 'predecessor_reserve_lower', 'reserve_gain')},
        'The exact complete larger J-neighborhood theorem, without mixing separate source budgets')
    reserve = family_bound['old49_replacement_reserve_lower']
    require(reserve == F(499570949, 75937500000), 'The certified whole rectangular J reserve')
    weight = F(jface['direction40_weight'])
    engine = load('source_barrier_saturation').Experiment(base)
    require(weight == engine.weights[40] > 0 and F(jface['old49_replacement_reserve']) == F(79, 1944)
            and all(pins.get(p) == v for p, v in engine.pins.items()),
            'The actual original complete direction40 coefficient and same source closure')
    near_low = fJ-a*d*d+weight*reserve
    require(reserve > 0 and near_low > 0, 'One original identity reserve removes the J near-source obstruction')

    locals_out = []
    for name, data in (('wide_fresh_full_slot_source_comparison', low), ('extended_source_bridge_comparison', wide)):
        c, heads, par = data['comparison'], data['complete_heads'], data['parameters']
        indices = [r['index'] for r in heads['mean_costs']+heads['quadratic_costs']+c['simple_costs']]+[0, 16, 46, 47]
        bound, den, num, offset = (F(c[k]) for k in ('comparison_upper', 'denominator_at_mass_floor', 'signed_endpoint', 'offset'))
        require(sorted(indices) == c['all_original_indices'] == list(range(52))
                and den > 0 and F(c['remaining_S_coefficient']) > 0
                and bound == offset+num/den < target and F(par['rbar']) == 5*F(par['rho']),
                'All original52 local costs, full denominators and actual mass/slot ranges')
        locals_out.append({'source': name, 'source_radius': F(par['delta']), 'residual_radius': F(par['rho']),
                           'complete_bound': bound, 'candidate_target_margin': target-bound})
    fallbacks = [{'branch': r['branch'], 'complete_bound': F(r['complete_bound']),
                  'candidate_target_gap': target-F(r['complete_bound'])} for r in old['fallbacks']]
    cores = [{'box': r['box'], 'unchanged_error': F(r['unchanged_error']),
              'candidate_complete_gap': target+F(r['unchanged_error'])-403} for r in old['complete_cores']]
    require(len(fallbacks) == 8 and min(r['candidate_target_gap'] for r in fallbacks) > 0
            and len(cores) == 2 and min(r['candidate_complete_gap'] for r in cores) > 0
            and F(old['positive_denominator_lower_factor']) > 0, 'Every fallback and terminal error remains; problem unresolved')
    return encode({'schema': 'erdos7-j-aggregate-layer-global-comparison-v1', 'source_sha256': pins,
        'old_K0': K0, 'previous198_K': F(old['candidate_K']), 'candidate_K': target,
        'original_paired_decrement_capacity': H, 'extra_decrement': extra, 'decrement_from_K0': h,
        'far_J_reserve_at_H': far_reserve, 'far_J_extra_payment': far_payment,
        'conservative_J_transition_t': t0,
        'improvement_over198': F(old['candidate_K'])-target,
        'original_allocation_conditional_sha256': stats['conditional_margin_sha256'],
        'complete_original_endpoint_table_sha256': control.digest(original),
        'same_source_denominator_table_sha256': control.digest(payments),
        'extended_layer_checks': layer_checks, 'target_floors': {'K': fK, 'J': fJ, 'B': fB, 'outside': fC},
        'aggregate_product_constraint': 'sqrt(qK+qB)+sqrt(qJ)<=1',
        'aggregate_lower_in_sqrt_J': 'fB+(fK-fB)*x+2u*z-(u+v)*z^2, z=sqrt(qJ),u=fC-fB,v=fC-fJ',
        'remaining_actual_residual_coefficient': Anew, 'sqrt_bracket_denominator': scale,
        'inner_complement_endpoints': inner_endpoints,
        'outer_K_mass_cap': cap, 'J_source_radius': d, 'J_residual_radius': R,
        'far_J_B_endpoint': far_B, 'far_J_start_endpoint': far_J_start,
        'far_J_end_endpoint': far_J_end, 'outer_sqrt_lower': lo, 'outer_sqrt_upper': hi,
        'near_J_high_residual_margin': near_high, 'complete_J_family_bound': family_bound,
        'J_identity_reserve': reserve, 'direction40_weight': weight,
        'near_J_low_residual_margin': near_low, 'local_complete_bounds': locals_out,
        'fallbacks': fallbacks, 'complete_cores': cores,
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'scope': 'Ordinary complete global comparison using the aggregate K/next-layer square-root exclusion. All four original paired layers are freshly checked at the new target before genuine-function Jensen. Both full local source rectangles, both inner alternatives, all three far-J endpoints and both near-J cases are covered. Only the true original old49 direction40 margin is replaced once using197 on its same actual source and residual. Every52 local cost, full denominator, eight fallbacks and both terminal errors remain. No Lean verification, actual-family sharpness or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true'); modes.add_argument('--check', action='store_true')
    args = parser.parse_args(); result = calculate(args.base)
    io = module('actual_j_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact complete aggregate-layer J-reserve global comparison')
    print('PASS: aggregate K/next exclusion, complete J reserve and full source union; global K='+str(float(F(result['candidate_K']))))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr); sys.exit(1)
