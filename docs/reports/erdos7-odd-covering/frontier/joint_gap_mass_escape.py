#!/usr/bin/env python3
"""Retain the original source gap and mass together before product Jensen.

The accompanying ordinary proof changes the coefficient of the true
separately concave D_c function, not the entries of an invented function.
This certificate checks the complete original table and the two endpoints
of the resulting affine family in the target decrement.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/joint_gap_mass_escape.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'frontier/k_next_escape_layers.py': 'f17140e366688960a1dcd04e3c72287c9acbeace1c865f0d1905a0d8d051a5b1',
    'certificates/source_norms/k_next_escape_layers.json': '68e181fcd4bb06953a03688260c8d426ee34c607bc73a5b5b8e49ee94fab00a8',
    'profile-notes/49-full-linear-and-quadratic-carriers-refine-the-frontier.md': 'fb65fb2a313b8cc937a0f1c5ac0314c1fc1cda55c045e27ffe1c2a70d107c931',
    'profile-notes/53-allocated-seven-thresholds-sharpen-actual-survival.md': 'e046b8ad8291b0b94963ce33a7ce10bf11710b972a872f8d7d8801c04fdab928',
    'profile-notes/71-global-j-k-control-faces-and-exact-escape-gaps.md': '1ba67485969c424f5523b77dd03a0dc0823f82f9d06f4c3dc719e9cfb66024c1',
    'profile-notes/94-quadratic-marked-events-and-a-common-residual-improve-global-k.md': '1307e769b1d1302fa83b9c1ca184b12b58eab377dc308999b2aaf207fb7f750e',
    'profile-notes/106-the-actual-denominator-shares-the-carrier-mass-residual.md': '312e9ee488aef11709b910308e4540f43cb396a5572d6a10a8d0e864cebedb29',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable original source')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [encode(v) for v in value]
    return value


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Pinned multipart input reader')
    io = module('gap_mass_io', base/'certificate_io.py')
    read = lambda name: json.loads(io.read_artifact_bytes(base/'certificates/source_norms'/(name+'.json')))
    prior = read('k_next_escape_layers')
    pins = dict(PINS)
    for path, pin in prior['source_sha256'].items():
        require(path not in pins or pins[path] == pin, 'Consistent inherited source '+path)
        pins[path] = pin
    for path, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned source '+path)
    predecessor = module('gap_mass_predecessor', base/'frontier/k_next_escape_layers.py')
    require(encode(predecessor.calculate(base)) == prior,
            'Reconstruct the complete original gap layers and product support constraints')
    control = module('gap_mass_control', base/'frontier/global_control_faces.py')
    source = module('gap_mass_source', base/'verify_joint_frontier.py')
    faces, survival, dictionary = (read(n) for n in
        ('global_control_faces', 'joint_survival_carriers', 'k_signed_gap_dictionary'))
    vertices = list(source.vertices())
    carriers = [tuple(c) for c in faces['carriers']]
    rows = [row for block in survival['joint_survival']['row_blocks'] for group in block for row in group]
    require(len(vertices) == len(rows) == dictionary['vertex_count'] == 1296
            and [row['index'] for row in rows] == list(range(1296)) and len(carriers) == 18,
            'Every original source vertex and full, partial or empty carrier')
    values = list(map(F, dictionary['rational_values']))
    lookup = dictionary['lower_gap_value_indices']
    require(len(lookup) == 1296*18 and all(type(j) is int and 0 <= j < len(values) for j in lookup),
            'Complete lower-gap dictionary')
    Kset = {(row['index'], row['carrier_index']) for row in faces['targets']['K']['zero_controls']}
    Jset = {(row['index'], row['carrier_index']) for row in faces['targets']['J']['zero_controls']}
    require(len(Kset) == 6 and len(Jset) == 18 and Kset.isdisjoint(Jset), 'Original disjoint control sets')
    A = F(faces['targets']['K']['mass_coefficient'])
    K0 = F(faces['targets']['K']['target'])
    g1, g2 = F(prior['first_positive_gap']), F(prior['gap_outside_JK_union'])
    dK, dJ = F(53, 360), F(3, 20)
    H = g1/dJ
    require(0 < 4*g1 < H < A and 0 < g1 < g2 and dJ-dK == F(1, 360)
            and K0 > source.WHOLE_CONST and source.AC > 0,
            'A positive remaining true mass coefficient and a strict gain over the old far capacity')
    table, lower, ratios = [], [], []
    for i, vertex in enumerate(vertices):
        raw = source.data(vertex)[3]
        for j, carrier in enumerate(carriers):
            row = rows[i]['conditional'][j]
            require(tuple(row['carrier']) == carrier, 'Same original carrier ordering')
            dc, gap = F(row['D_c']), values[lookup[18*i+j]]
            require(0 < dc <= raw and gap >= 0, 'Original positive mass interval and signed lower gap')
            table.extend(((i, j, 'D_c', gap), (i, j, 's', gap+A*(raw-dc))))
            lower.append((i, j, dc, raw, gap))
            if (i, j) not in Kset:
                ratios.extend(((gap/dc, i, j, 'D_c'), ((gap+A*(raw-dc))/raw, i, j, 's')))
            if (i, j) in Kset:
                require(dc == dK and gap == 0 and raw == F(1, 4), 'Exact K gap and mass')
            elif (i, j) in Jset:
                require(dc == dJ and gap == g1 and raw == F(1, 4), 'Exact J gap and mass')
    digest = control.digest(table)
    require(digest == prior['complete_original_endpoint_table_sha256']
            == faces['targets']['K']['all_signed_gaps_sha256'], 'Unchanged full46656-endpoint table')
    min_ratio = min(row[0] for row in ratios)
    controls = [(i, j, endpoint) for ratio, i, j, endpoint in ratios if ratio == min_ratio]
    require(min_ratio == H and {(i, j) for i, j, endpoint in controls} == Jset
            and len(controls) == 18 and all(endpoint == 'D_c' for i, j, endpoint in controls),
            'The joint gap/mass capacity is attained exactly at the18 J lower endpoints')

    decrement_checks = []
    for h in (F(0), H):
        k_floor, j_floor, outside_floor = -h*dK, g1-h*dJ, g2-h*dK
        outside = []
        for i, j, dc, raw, gap in lower:
            floor = k_floor if (i, j) in Kset else j_floor if (i, j) in Jset else outside_floor
            margin = gap-h*dc-floor
            require(margin >= 0, 'Every lower endpoint satisfies the layer bound at both decrement endpoints')
            require(gap+A*(raw-dc)-h*raw-floor == margin+(A-h)*(raw-dc) >= 0,
                    'The same layer bound holds at the upper actual-mass endpoint')
            if (i, j) not in Kset | Jset:
                outside.append((margin, i, j))
        witnesses = [(i, j) for margin, i, j in outside if margin == 0]
        require(witnesses == [(386, 14), (592, 13)] and outside_floor > j_floor >= 0,
                'Exact next controls and a positive coefficient for the product exclusion')
        decrement_checks.append({'decrement': h, 'K_floor': k_floor, 'J_floor': j_floor,
                                 'outside_floor': outside_floor, 'outside_controllers': witnesses,
                                 'lower_endpoint_checks': len(lower), 'upper_endpoint_checks': len(lower),
                                 'minimum_outside_margin': min(row[0] for row in outside)})
    # All endpoint inequalities above are affine in h. These two complete
    # checks prove them for every h in [0,H], rather than a sampled h-grid.
    require(A-H > 0 and g2-g1 > 0 and g2-g1+H*(dJ-dK) > 0,
            'Separate concavity survives the mass-coefficient change; the final sigma polynomial is concave')
    envelope = lambda h, s: g2*s-(g2-g1)*s*s-h*(dK+(dJ-dK)*s*s)
    far_half, far_one = envelope(H, F(1, 2)), envelope(H, F(1))
    eta = g2-H*dK
    require(far_half > 0 and far_one == 0 and eta > 0
            and far_half == (eta/2-H*dK)/2,
            'The entire far interval is covered at the maximal joint decrement')
    transition = H*dK/eta
    require(0 < transition < F(1, 2)
            and envelope(H, transition) == 0,
            'The exact lower root of the maximal-decrement polynomial')
    endpoint_rows = [{'index': i, 'carrier_index': j, 'carrier': carriers[j],
                      'endpoint': endpoint, 'gap_over_mass': H}
                     for i, j, endpoint in controls]
    return encode({'schema': 'erdos7-joint-gap-mass-escape-v1', 'source_sha256': pins,
        'complete_original_endpoint_table_sha256': digest, 'original_endpoint_checks': len(table),
        'old_K0': K0, 'signed_mass_coefficient': A,
        'K_lower_mass': dK, 'J_lower_mass': dJ, 'first_escape_gap': g1, 'next_escape_gap': g2,
        'decrement_capacity': H, 'old_far_decrement_capacity': 4*g1,
        'capacity_improvement': H-4*g1, 'capacity_ratio_to_old_far': H/(4*g1),
        'mass_coefficient_at_capacity': A-H,
        'complete_decrement_endpoint_checks': decrement_checks,
        'nonK_mass_endpoint_ratio_checks': len(ratios), 'minimum_nonK_gap_over_mass': min_ratio,
        'minimum_ratio_controls': endpoint_rows,
        'continuum_domain': {'source_escape': '0<=sigma=1-qK<=1', 'decrement': '0<=h<=decrement_capacity',
                             'actual_residual': 'rho=S-sum_c pi_c*D_c(theta)>=0'},
        'true_function_jensen_bridge': 'Phi(K0-h)>=sum_vc Lambda_v*pi_c*(g_vc(D_c(v))-h*D_c(v))+(A-h)*rho',
        'layered_bound': '-h*dK*qK+(gamma1-h*dJ)*qJ+(gamma2-h*dK)*(1-qK-qJ)+(A-h)*rho',
        'product_exclusion': 'qJ<=(1-qK)^2=sigma^2',
        'joint_envelope': 'Phi(K0-h)>=gamma2*sigma-(gamma2-gamma1)*sigma^2-h*(53/360+sigma^2/360)+(A-h)*rho',
        'joint_payment_constant': dK, 'joint_payment_sigma_squared_coefficient': dJ-dK,
        'capacity_polynomial_factorization': '(1-sigma)*((gamma2-H*dK)*sigma-H*dK)',
        'capacity_lower_root': transition, 'far_interval': (F(1, 2), F(1)),
        'far_endpoint_margins_at_capacity': (far_half, far_one),
        'scope': 'Ordinary theorem on every original effective actual source, with the original carrier mixture, independent numerator labels and full tails. The displayed quadratic payment is a combined signed-gap estimate, not an upper bound on the actual denominator or S0. The true separately concave mass function is reweighted before product Jensen. The whole far interval supports h=(20/3)*gamma1; no joined full-global comparison, actual attainment, Lean verification or unrestricted Erdos7 resolution is claimed.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[1])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('gap_mass_writer', args.base/'certificate_io.py')
    if args.write:
        io.write_certificate_text(args.base/CERTIFICATE, json.dumps(result, indent=2)+'\n')
    elif args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result,
                'Exact original-source joint gap/mass certificate')
    print('PASS: full original table, true-source mass reweighting and far interval; h='
          +str(float(F(result['decrement_capacity'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
