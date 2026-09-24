#!/usr/bin/env python3
"""Keep the next source layer and its beta-factor conflict with the J layer.

Recover every allocated survival margin with the exact original53 provider.
Its complete conditional digest identifies the same M used by the old71
gap table; no independently selected denominator bound is subtracted.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/cover-geometry/three_layer_product_escape.json'
PINS = {
    'certificates/source_norms/endpoint-bounds/k_next_escape_layers.json': 'bcde35a6249003e95c6a39dc6b2bee3fa3d03be18291927385ae6dca4c896270',
    'frontier/endpoint-bounds/k_next_escape_layers.py': 'd7c51cf6f2becc96392fdae6318661aab37ee204edd82769c2f3668e1d657500',
    'certificates/source_norms/cover-geometry/joint_gap_denominator_escape.json': '414d035791892a6d9e8cf16e522b58e7257b99743e845ce5a882aa94bce783e5',
    'frontier/cover-geometry/joint_gap_denominator_escape.py': 'bc5bd10d49a0e1df10fac0a5f6e6f6f931e0a87808e587aca35fcc55bebad52f',
    'certificate_io.py': '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b',
    'frontier/cover-geometry/joint_gap_mass_escape.py': '0dbba25ea2058da3a2aa3936f0ad96fae6ef34fc085e6b0cba099225e64c9ffc',
    'certificates/source_norms/cover-geometry/joint_gap_mass_escape.json': 'a942be9516a3626357445af191df6195f827be18008aa0d52ee43cdf5f68ca89',
    'frontier/comparison-bounds/allocated_seven_thresholds.py': 'b467824a30899cd14ab35ab4a1383c4a3848e5c9dcbdaebd6f4074e9a1d8e78d',
    'certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json': '3b8afa03444fe045c9dba7e1a74ac051c3d4032eddfeae106a47e360ad0d34e2',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original provider')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned multipart input reader')
    io = module('joint_denominator_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(io.named_artifact(base/'certificates/source_norms', name+'.json')))
    previous = read('joint_gap_mass_escape')
    previous_denominator = read('joint_gap_denominator_escape')
    layers = read('k_next_escape_layers')
    pins = dict(PINS)
    for path, pin in {**previous['source_sha256'], **previous_denominator['source_sha256'], **layers['source_sha256']}.items():
        require(path not in pins or pins[path] == pin, 'Consistent original source '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input '+path)
    prior = module('joint_denominator_prior', base/'frontier/cover-geometry/joint_gap_mass_escape.py')
    require(prior.calculate(base) == previous, 'Reconstruct the unchanged gap table and source product constraints')
    source = module('joint_denominator_source', base/'verify_joint_frontier.py')
    allocated = module('joint_denominator_allocated', base/'frontier/comparison-bounds/allocated_seven_thresholds.py')
    control = module('joint_denominator_control', base/'frontier/source-budgets/global_control_faces.py')
    old53, faces, survival, dictionary = (read(n) for n in
        ('allocated_seven_thresholds', 'global_control_faces', 'joint_survival_carriers', 'k_signed_gap_dictionary'))
    vertices = list(source.vertices())
    source_metadata = []
    for index, vertex in enumerate(vertices):
        dat = source.data(vertex)
        source_metadata.append({'index': index, 's': dat[3], 'D': dat[4]})
    # The original allocation routine reads only s,D from rows39. Its source
    # functions and old conditional margins are reconstructed without changing
    # that routine or inventing uncomputed numerator data in the metadata.
    rows, statistics = allocated.reconstruct(source, survival, source_metadata)
    require(encode(statistics) == old53['allocation_statistics'],
            'Every original53 allocation statistic and the complete conditional-margin digest')
    require(statistics['old_margin_checks'] == 46656 and len(rows) == 1296,
            'Fresh reconstruction of every full and partial original survival margin')
    Q, K0, offset, A = allocated.Q, F(previous['old_K0']), source.WHOLE_CONST, F(previous['signed_mass_coefficient'])
    slope = source.AC*F(old53['H16'])+F(old53['H41'])+F(old53['A81'])
    require(Q == F(23, 42) == F(old53['q_effective']) and K0 == F(old53['combined'])
            and A == Q*(K0-offset)-slope == F(old53['coefficients']['combined']),
            'The actual original53 target, offset, complete numerator slope and mass coefficient')
    g1, g2 = F(previous['first_escape_gap']), F(previous['next_escape_gap'])
    Kset = {(r['index'], r['carrier_index']) for r in faces['targets']['K']['zero_controls']}
    Jset = {(r['index'], r['carrier_index']) for r in faces['targets']['J']['zero_controls']}
    require(len(Kset) == 6 and len(Jset) == 18 and Kset.isdisjoint(Jset), 'The same original control sets')
    values = list(map(F, dictionary['rational_values']))
    lookup = dictionary['lower_gap_value_indices']
    require(len(lookup) == len(rows)*18 and all(type(j) is int and 0 <= j < len(values) for j in lookup),
            'Complete original gap lookup')
    table, lower, ratios, complete_payments = [], [], [], []
    for i, row in enumerate(rows):
        require(row['index'] == i and len(row['conditional']) == 18, 'Original complete source/carrier ordering')
        raw = row['s']
        for j, cond in enumerate(row['conditional']):
            require(tuple(cond['carrier']) == allocated.CARRIERS[j] == tuple(faces['carriers'][j]),
                    'The same source carrier in the gap and original allocated margin')
            dc, margin = cond['D_c'], cond['M']
            gap = values[lookup[18*i+j]]
            payment = Q*dc+margin
            require(0 < payment <= dc <= raw and gap >= 0,
                    'Original positive source denominator and actual mass interval')
            table.extend(((i, j, 'D_c', gap), (i, j, 's', gap+A*(raw-dc))))
            lower.append((i, j, dc, raw, margin, payment, gap))
            complete_payments.append((i, j, dc, margin, payment))
            if (i, j) not in Kset:
                ratios.extend(((gap/payment, i, j, 'D_c'),
                               ((gap+A*(raw-dc))/(Q*raw+margin), i, j, 's')))
    require(control.digest(table) == previous['complete_original_endpoint_table_sha256'],
            'Every gap still belongs to the unchanged original71 full endpoint table')
    eK = F(240585528019, 3208936500000)
    eJ = F(40593580507, 534822750000)
    eB = F(34755559087, 458419500000)
    H = g1/eJ
    require(all(payment == eK and gap == 0 for i, j, dc, raw, margin, payment, gap in lower if (i, j) in Kset)
            and all(payment == eJ and gap == g1 for i, j, dc, raw, margin, payment, gap in lower if (i, j) in Jset),
            'The exact same-source denominator payments on K and J')
    require(0 < eK < eB < eJ < F(3, 20) and 0 < F(previous['decrement_capacity']) < H
            and A-Q*H > 0 and K0-offset-H > 0,
            'Strict improvement while both true concave-function coefficients remain positive')
    nextset = {(r['index'], r['carrier_index']) for r in layers['next_layer_controls']}
    require(nextset == {(386, 14), (592, 13)}, 'Original next layer with its exact beta support')
    g3 = F(layers['gap_outside_extended_union'])
    eC = F(11635969547, 152806500000)
    endpoint_checks = []
    for h in (F(0), H):
        floors = (-h*eK, g1-h*eJ, g2-h*eB, g3-h*eC)
        outside = []
        for i, j, dc, raw, margin, payment, gap in lower:
            floor = floors[0] if (i, j) in Kset else floors[1] if (i, j) in Jset else floors[2] if (i, j) in nextset else floors[3]
            slack = gap-h*payment-floor
            require(slack >= 0, 'Every original lower endpoint satisfies its jointly reweighted layer')
            require(gap+A*(raw-dc)-h*(Q*raw+margin)-floor
                    == slack+(A-Q*h)*(raw-dc) >= 0,
                    'Every original upper endpoint retains the same survival margin')
            if (i, j) not in Kset | Jset | nextset:
                outside.append((slack, i, j, payment))
        witnesses = [(i, j) for slack, i, j, payment in outside if slack == 0]
        require(witnesses == [(386, 15), (386, 16), (386, 17), (592, 15), (592, 16), (592, 17)]
                and all(payment == eC for slack, i, j, payment in outside if slack == 0)
                and floors[3] > floors[2] > floors[1] >= 0,
                'The same exact next controls at both decrement endpoints')
        endpoint_checks.append({'decrement': h, 'K_floor': floors[0], 'J_floor': floors[1],
            'next_floor': floors[2], 'outside_floor': floors[3], 'outside_controllers': witnesses,
            'lower_checks': len(lower), 'upper_checks': len(lower),
            'minimum_outside_slack': min(slack for slack, i, j, payment in outside)})
    controls = [(i, j, endpoint) for ratio, i, j, endpoint in ratios if ratio == H]
    require(min(ratio for ratio, i, j, endpoint in ratios) == H
            and len(controls) == 18 and {(i, j) for i, j, endpoint in controls} == Jset
            and all(endpoint == 'D_c' for i, j, endpoint in controls),
            'The exact nonK gap/denominator ratio capacity and all its controls')
    require(0 < eK < eB < eJ < eC and g3 > g2 > g1,
            'The same original source rows carry four ordered joint layers')
    for h in (F(0), H):
        fK, fJ, fB, fC = -h*eK, g1-h*eJ, g2-h*eB, g3-h*eC
        require(fC > fB > fJ >= 0 and fK <= 0,
                'Nonnegative weights in the beta-factor auxiliary optimization')
        require(fK-fB < 0 and fK+fJ-2*fC < 0,
                'Both resulting alternatives are concave in sqrt(qK)')
    return encode({'schema': 'erdos7-three-layer-product-escape-v1', 'source_sha256': pins,
        'original_allocation_conditional_sha256': statistics['conditional_margin_sha256'],
        'fresh_old_margin_reconstruction_checks': statistics['old_margin_checks'],
        'same_source_denominator_table_sha256': control.digest(complete_payments),
        'complete_original_endpoint_table_sha256': control.digest(table),
        'original_endpoint_checks': len(table), 'old_K0': K0, 'old_offset': offset,
        'signed_mass_coefficient': A, 'survival_mass_coefficient': Q,
        'first_escape_gap': g1, 'next_escape_gap': g2, 'third_escape_gap': g3,
        'K_denominator_payment': eK, 'J_denominator_payment': eJ,
        'next_denominator_payment': eB, 'third_denominator_payment': eC,
        'decrement_capacity': H, 'complete_decrement_endpoint_checks': endpoint_checks,
        'beta_product_constraints': ['qK=b*k', 'qJ=b*j', 'qA<=(1-b)*k', 'sqrt(k)+sqrt(j)<=1'],
        'fixed_qK_optimization': 'max over t in [sqrt(qK),1] of u*t^2+v*qK*(1/t-1)^2; u=fC-fB>0,v=fC-fJ>0',
        'auxiliary_second_derivative': '2u+v*qK*(6/t^4-4/t^3)>0',
        'next_layer_alternative': 'fK*(1-sigma)+fB*sigma',
        'J_layer_alternative': 'fK*t^2+fJ*(1-t)^2+2*fC*t*(1-t), t=sqrt(1-sigma)',
        'joint_lower_bound': 'Phi(K0-h)>=min(next_layer_alternative,J_layer_alternative)+(A-q*h)*rho',
        'scope': 'Ordinary complete actual-source theorem preserving the original beta, late and carrier product factors. The next and J layer masses cannot be independently maximized. A convex one-variable auxiliary optimization gives two endpoint alternatives, both concave in sqrt(qK). All four joint gap/denominator layer floors are checked at both h endpoints against every original row. Original labels, one actual residual and full tails remain. No complete global join, actual-family attainment, Lean verification or Erdos7 resolution.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('joint_denominator_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Exact beta-separated three-layer source certificate')
    print('PASS: complete paired third layer and beta-product endpoint alternatives; h='
          +str(float(F(result['decrement_capacity'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
