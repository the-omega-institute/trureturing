#!/usr/bin/env python3
"""Use complete wider source domains and their wholly unmarked complement."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/comparison-bounds/wide_unmarked_union_comparison.json'
PINS = {'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2', 'frontier/source-budgets/capped_slot_outer_comparison.py': '287a31898f62df16e55211540c639fd968e9f8e845e7b7751fc787979181fa7e', 'certificates/source_norms/source-budgets/capped_slot_outer_comparison.json': 'f4cadcf33b6c297f7bf568f5387a8895fe10ded68152a31b74fac541df1031b2', 'frontier/source-budgets/wide_fresh_full_slot_source_comparison.py': 'f4cb79e71f5092d0eeca452aba9bbb31e9fc8ea929685cbdfa462ea269cd19d9', 'certificates/source_norms/source-budgets/wide_fresh_full_slot_source_comparison.json': 'f5fa0d812a9a5330585948683fa9e93dc4a405a7e2d962973cb189b0ae1f3a04', 'frontier/retained-transport/transported_source_complete_comparison.py': '361c6ba33a0d78abae5238656412a4caa8470f5a10ee1c9667245bb72c4bd8c2', 'certificates/source_norms/retained-transport/transported_source_complete_comparison.json': 'dc50465cb2af888f04b2e6430a185f9083f88fa55963a7687e974fa9df01cc46'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original result')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def calculate(base):
    require(PINS, 'Both complete domains and the old full comparison must be pinned')
    io = module('wide_union_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    names = ('capped_slot_outer_comparison', 'wide_fresh_full_slot_source_comparison',
             'transported_source_complete_comparison')
    inputs = {name: read(name) for name in names}
    pins = dict(PINS)
    for data in inputs.values():
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent complete source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    old = inputs[names[0]]
    prior = module('wide_union_prior', base/'frontier/source-budgets/capped_slot_outer_comparison.py')
    require(prior.calculate(base) == old, 'Reconstruct the complete preceding global comparison')
    local, wide = inputs[names[1]], inputs[names[2]]
    p0 = {k: F(local['parameters'][k]) for k in ('delta', 'rho', 'rbar')}
    p1 = {k: F(wide['parameters'][k]) for k in ('delta', 'rho', 'rbar')}
    s0, R0, s1, R1 = p0['delta'], p0['rho'], p1['delta'], p1['rho']
    require((s0, R0, p0['rbar']) == (F(1, 20), F(1, 1000), F(1, 200))
            and (s1, R1, p1['rbar']) == (F(1, 18), F(1, 13000), F(1, 2600))
            and p0['rbar'] == 5*R0 and p1['rbar'] == 5*R1,
            'Each complete rectangle includes every actual slot loss allowed by r<=5rho')
    source, mass_source = read('shared_slot_gap_global'), read('joint_mass_outer_comparison')
    A, a, b, g1, g2, K0 = (F(source[k]) for k in ('conservative_mass_coefficient',
        'S0_upper_constant', 'S0_upper_sigma_coefficient', 'first_escape_gap', 'next_escape_gap', 'old_K0'))
    limit, slope = F(mass_source['signed_mass_limit']), F(mass_source['signed_mass_slope'])
    require(0 < R1 < R0 and 0 < s0 < s1 < limit == F(1, 3) and slope == F(1, 10),
            'All low and bridge mass bounds remain within the signed-mass domain')
    escape = lambda s: g2*s-(g2-g1)*s*s
    rows = []

    def endpoint(branch, sigma, rho, mass):
        reserve, payment = escape(sigma)+A*rho, mass+rho
        require(reserve > 0 and payment > 0, 'Positive complete endpoint and payment')
        rows.append({'branch': branch, 'sigma': sigma, 'residual_lower': rho,
                     'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                     'decrement_capacity': reserve/payment})

    for s, tag in ((F(0), 'zero'), (s0, 'low_radius')):
        endpoint('low_'+tag, s, R0, a+slope*s)
    for s, tag in ((s0, 'low_radius'), (s1, 'wide_radius')):
        endpoint('bridge_'+tag, s, R1, a+slope*s)
    for s, tag in ((s1, 'wide_radius'), (limit, 'joint_limit')):
        endpoint('early_'+tag, s, F(0), a+slope*s)
    for s, tag in ((limit, 'joint_limit'), (F(1, 2), 'half')):
        endpoint('middle_'+tag, s, F(0), a+b*s)
    for s, tag in ((F(1, 2), 'half'), (F(1), 'one')):
        endpoint('far_'+tag, s, F(0), F(1, 4)+F(11, 36)*s*(1-s))
    require(len(rows) == 10, 'Both endpoints of all five exhaustive complement intervals')
    h = min(row['decrement_capacity'] for row in rows)
    controllers = [row['branch'] for row in rows if row['decrement_capacity'] == h]
    require(controllers == ['far_one'] and h == 4*g1, 'The zero-K source endpoint now controls')
    require(A-h > 0 and g2-g1 > 0 and g2-g1-F(11, 36)*h > 0,
            'Same-residual monotonicity and every source-interval concavity')
    for row in rows:
        row['margin'] = row['reserve_at_K0']-h*row['target_payment_coefficient']
    require(sum(row['margin'] == 0 for row in rows) == 1 and all(row['margin'] >= 0 for row in rows),
            'Unique controlling endpoint and nonnegative complete interval bounds')
    target = K0-h
    locals = []
    for name, data, par in ((names[1], local, p0), (names[2], wide, p1)):
        c = data['comparison']
        bound = F(c['comparison_upper'])
        require(c['all_original_indices'] == list(range(52)) and F(c['denominator_at_mass_floor']) > 0
                and F(c['remaining_S_coefficient']) > 0 and bound < target,
                'Every complete actual-source comparison is strictly below this global target')
        locals.append({'source': name, 'source_radius': par['delta'], 'residual_radius': par['rho'],
                       'implied_slot_radius': par['rbar'], 'complete_bound': bound})
    fallbacks = []
    for row in old['fallbacks']:
        bound = F(row['complete_bound'])
        require(bound < target, 'The original complete fallback lies below the new target')
        fallbacks.append({'branch': row['branch'], 'complete_bound': bound, 'candidate_target_gap': target-bound})
    cores = []
    for row in old['complete_cores']:
        error = F(row['unchanged_error'])
        require(error >= 0 and target+error > 403, 'Every complete terminal error remains; unrestricted problem unresolved')
        cores.append({'box': row['box'], 'unchanged_error': error, 'candidate_complete_gap': target+error-403})
    require(len(fallbacks) == 8 and len(cores) == 2
            and F(old['positive_denominator_lower_factor']) > 0
            and F(source['old_mass_coefficient'])-F(23, 42)*h > 0 and target < F(old['candidate_K']),
            'All original branches, positive division and a strict global improvement')
    return module('wide_union_encoder', base/'frontier/source-budgets/full_slot_union_outer_comparison.py').encode({
        'schema': 'erdos7-wide-unmarked-union-comparison-v1', 'source_sha256': pins,
        'low_source_radius': s0, 'low_residual_radius': R0, 'wide_source_radius': s1, 'wide_residual_radius': R1,
        'old_K0': K0, 'decrement_from_K0': h, 'candidate_K': target,
        'previous177_K': F(old['candidate_K']), 'improvement_over177': F(old['candidate_K'])-target,
        'unmarked_residual_coefficient': A-h, 'complete_outer_endpoints': rows,
        'controlling_branches': controllers, 'local_complete_bounds': locals,
        'fallbacks': fallbacks, 'complete_cores': cores,
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'scope': 'Ordinary full global comparison joining181 and170 complete actual-source rectangles. Their entire complement uses the existing unmarked reserve and signed mass bounds, with no marked-domain extrapolation. Ten endpoints, eight original fallback branches, two complete terminal errors and all original independent labels/infinite tails remain. Canonical118 unchanged; no Lean verification or unrestricted Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('wide_union_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact wider unmarked union certificate')
    print('PASS: ten unmarked endpoints and complete original branches; K='+str(float(F(result['candidate_K'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
