#!/usr/bin/env python3
"""Join complete source domains using the same-source signed gap and mass."""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/joint_gap_mass_global_comparison.json'
PINS = {'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b', 'frontier/comparison-bounds/wide_unmarked_union_comparison.py': 'd6420f4ecefd22ed22c7e4cb44f3b9d8d6a2b355cd52da8525125f9425373c23', 'certificates/source_norms/comparison-bounds/wide_unmarked_union_comparison.json': '2597213116bb0277589f484aaf105b7db2e5950f7c53c2df608b0a68caf80c5f', 'frontier/cover-geometry/joint_gap_mass_escape.py': '0dbba25ea2058da3a2aa3936f0ad96fae6ef34fc085e6b0cba099225e64c9ffc', 'certificates/source_norms/cover-geometry/joint_gap_mass_escape.json': 'a942be9516a3626357445af191df6195f827be18008aa0d52ee43cdf5f68ca89', 'frontier/source-budgets/wide_fresh_full_slot_source_comparison.py': '4180ce2f7cb27179e7f8f10092d31c61f7da90e4c03623c07ff796c43f9a599d', 'certificates/source_norms/source-budgets/wide_fresh_full_slot_source_comparison.json': '31f20d1d614a6b961fe00642340a9fc3b5ac61d16862e02617337dabbbd8d427', 'frontier/retained-transport/transported_source_complete_comparison.py': '68eff34e6592cfc5c6dbac23aacef6bfb1f5bed1c8ff8f74560c6ec387299418', 'certificates/source_norms/retained-transport/transported_source_complete_comparison.json': '100449a6e36be50d2ba5cb1808929cc2107f447e2b5a43076caed4ee542c4692'}


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
    names = ('wide_unmarked_union_comparison', 'wide_fresh_full_slot_source_comparison',
             'transported_source_complete_comparison', 'joint_gap_mass_escape')
    inputs = {name: read(name) for name in names}
    pins = dict(PINS)
    for data in inputs.values():
        for path, pin in data['source_sha256'].items():
            require(path not in pins or pins[path] == pin, 'Consistent complete source '+path)
            pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    old = inputs[names[0]]
    joint = inputs['joint_gap_mass_escape']
    source_proof = module('joint_global_source_proof', base/'frontier/cover-geometry/joint_gap_mass_escape.py')
    require(source_proof.calculate(base) == joint, 'Reconstruct the new joint source-payment theorem')
    local, wide = inputs[names[1]], inputs[names[2]]
    p0 = {k: F(local['parameters'][k]) for k in ('delta', 'rho', 'rbar')}
    p1 = {k: F(wide['parameters'][k]) for k in ('delta', 'rho', 'rbar')}
    s0, R0, s1, R1 = p0['delta'], p0['rho'], p1['delta'], p1['rho']
    require((s0, R0, p0['rbar']) == (F(1, 20), F(1, 1000), F(1, 200))
            and (s1, R1, p1['rbar']) == (F(1, 18), F(1, 13000), F(1, 2600))
            and p0['rbar'] == 5*R0 and p1['rbar'] == 5*R1,
            'Each complete rectangle includes every actual slot loss allowed by r<=5rho')
    A, g1, g2, K0, H, dK, dQ = (F(joint[k]) for k in (
        'signed_mass_coefficient', 'first_escape_gap', 'next_escape_gap', 'old_K0',
        'decrement_capacity', 'joint_payment_constant', 'joint_payment_sigma_squared_coefficient'))
    require(0 < R1 < R0 and 0 < s0 < s1 < 1 and dK == F(53, 360) and dQ == F(1, 360)
            and K0 == F(old['old_K0']) and H == F(20, 3)*g1,
            'The original target and the full-source quadratic payment are retained')
    escape = lambda s: g2*s-(g2-g1)*s*s
    rows = []

    def endpoint(branch, sigma, rho):
        reserve, payment = escape(sigma)+A*rho, dK+dQ*sigma*sigma+rho
        require(reserve > 0 and payment > 0, 'Positive complete endpoint and payment')
        rows.append({'branch': branch, 'sigma': sigma, 'residual_lower': rho,
                     'reserve_at_K0': reserve, 'target_payment_coefficient': payment,
                     'decrement_capacity': reserve/payment})

    for s, tag in ((F(0), 'zero'), (s0, 'low_radius')):
        endpoint('low_'+tag, s, R0)
    for s, tag in ((s0, 'low_radius'), (s1, 'wide_radius')):
        endpoint('bridge_'+tag, s, R1)
    for s, tag in ((s1, 'wide_radius'), (F(1), 'one')):
        endpoint('outer_'+tag, s, F(0))
    require(len(rows) == 6, 'Both endpoints of all three exhaustive complement intervals')
    h = min(row['decrement_capacity'] for row in rows)
    controllers = [row['branch'] for row in rows if row['decrement_capacity'] == h]
    require(controllers == ['outer_wide_radius'] and 0 < h < H,
            'The complete source-radius boundary uniquely controls within the proved decrement interval')
    require(A-h > 0 and g2-g1+h*dQ > 0,
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
            and A-F(23, 42)*h > 0 and target < F(old['candidate_K']),
            'All original branches, positive division and a strict global improvement')
    return module('wide_union_encoder', base/'frontier/source-budgets/full_slot_union_outer_comparison.py').encode({
        'schema': 'erdos7-joint-gap-mass-global-comparison-v1', 'source_sha256': pins,
        'low_source_radius': s0, 'low_residual_radius': R0, 'wide_source_radius': s1, 'wide_residual_radius': R1,
        'old_K0': K0, 'decrement_from_K0': h, 'candidate_K': target,
        'previous179_K': F(old['candidate_K']), 'improvement_over179': F(old['candidate_K'])-target,
        'proved_decrement_limit': H, 'joint_payment_constant': dK,
        'joint_payment_sigma_squared_coefficient': dQ,
        'unmarked_residual_coefficient': A-h, 'complete_outer_endpoints': rows,
        'controlling_branches': controllers, 'local_complete_bounds': locals,
        'fallbacks': fallbacks, 'complete_cores': cores,
        'positive_denominator_lower_factor': F(old['positive_denominator_lower_factor']),
        'scope': 'Ordinary full global comparison joining181 and170 complete actual-source rectangles. Their entire complement uses183 true-source signed gap/mass interpolation, with one actual residual. The quadratic target payment is not asserted to bound mass separately. Six endpoints, eight original fallback branches, two complete terminal errors and all original independent labels/infinite tails remain. Canonical118 unchanged; no Lean verification or unrestricted Erdos7 resolution.'})


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
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Exact joint-source global certificate')
    print('PASS: six joint-source endpoints and complete original branches; K='+str(float(F(result['candidate_K'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
