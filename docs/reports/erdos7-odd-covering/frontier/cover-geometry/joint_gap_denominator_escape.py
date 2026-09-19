#!/usr/bin/env python3
"""Reweight both original positive coefficients before source interpolation.

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
CERTIFICATE = 'certificates/source_norms/cover-geometry/joint_gap_denominator_escape.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/cover-geometry/joint_gap_mass_escape.py': '11b3195c2c215ecd886216e15b387e8913692b9de37d9e96f00c6479a237a3b6',
    'certificates/source_norms/cover-geometry/joint_gap_mass_escape.json': 'fac5fcbf784c91c5b66a80ecc3e652e75fde821adedbaae5ce8d532d49b75c80',
    'frontier/comparison-bounds/allocated_seven_thresholds.py': 'b467824a30899cd14ab35ab4a1383c4a3848e5c9dcbdaebd6f4074e9a1d8e78d',
    'certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json': 'ec6c4cf8b2c2f53179eead3d0a7499ca69fb796d57df6b65a91b0d672745a1b5',
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
    pins = dict(PINS)
    for path, pin in previous['source_sha256'].items():
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
    endpoint_checks = []
    for h in (F(0), H):
        floors = (-h*eK, g1-h*eJ, g2-h*eB)
        outside = []
        for i, j, dc, raw, margin, payment, gap in lower:
            floor = floors[0] if (i, j) in Kset else floors[1] if (i, j) in Jset else floors[2]
            slack = gap-h*payment-floor
            require(slack >= 0, 'Every original lower endpoint satisfies its jointly reweighted layer')
            require(gap+A*(raw-dc)-h*(Q*raw+margin)-floor
                    == slack+(A-Q*h)*(raw-dc) >= 0,
                    'Every original upper endpoint retains the same survival margin')
            if (i, j) not in Kset | Jset:
                outside.append((slack, i, j, payment))
        witnesses = [(i, j) for slack, i, j, payment in outside if slack == 0]
        require(witnesses == [(386, 14), (592, 13)]
                and all(payment == eB for slack, i, j, payment in outside if slack == 0)
                and floors[2] > floors[1] >= 0,
                'The same exact next controls at both decrement endpoints')
        endpoint_checks.append({'decrement': h, 'K_floor': floors[0], 'J_floor': floors[1],
            'outside_floor': floors[2], 'outside_controllers': witnesses,
            'lower_checks': len(lower), 'upper_checks': len(lower),
            'minimum_outside_slack': min(slack for slack, i, j, payment in outside)})
    controls = [(i, j, endpoint) for ratio, i, j, endpoint in ratios if ratio == H]
    require(min(ratio for ratio, i, j, endpoint in ratios) == H
            and len(controls) == 18 and {(i, j) for i, j, endpoint in controls} == Jset
            and all(endpoint == 'D_c' for i, j, endpoint in controls),
            'The exact nonK gap/denominator ratio capacity and all its controls')
    c0, c1, c2 = eK, eB-eK, eJ-eB
    require(c1 == F(90112853, 106964550000) and c2 == F(272569433, 3208936500000)
            and g2-g1+H*c2 > 0, 'Exact joint payment polynomial and source concavity')
    envelope = lambda h, s: g2*s-(g2-g1)*s*s-h*(c0+c1*s+c2*s*s)
    eta = g2-H*eB
    far_half, far_one = envelope(H, F(1, 2)), envelope(H, F(1))
    transition = H*eK/eta
    require(eta > 0 and 0 < transition < F(1, 2) and far_half > 0 and far_one == 0
            and envelope(H, transition) == 0 and far_half == (eta/2-H*eK)/2,
            'The maximal-decrement factorization covers the whole far interval')
    return encode({'schema': 'erdos7-joint-gap-denominator-escape-v1', 'source_sha256': pins,
        'original_allocation_conditional_sha256': statistics['conditional_margin_sha256'],
        'fresh_old_margin_reconstruction_checks': statistics['old_margin_checks'],
        'same_source_denominator_table_sha256': control.digest(complete_payments),
        'complete_original_endpoint_table_sha256': control.digest(table),
        'original_endpoint_checks': len(table), 'old_K0': K0, 'old_offset': offset,
        'signed_mass_coefficient': A, 'survival_mass_coefficient': Q,
        'first_escape_gap': g1, 'next_escape_gap': g2,
        'K_denominator_payment': eK, 'J_denominator_payment': eJ, 'next_denominator_payment': eB,
        'decrement_capacity': H, 'previous_mass_capacity': F(previous['decrement_capacity']),
        'capacity_improvement': H-F(previous['decrement_capacity']),
        'remaining_mass_coefficient_at_capacity': A-Q*H,
        'remaining_survival_margin_coefficient_at_capacity': K0-offset-H,
        'complete_decrement_endpoint_checks': endpoint_checks,
        'nonK_mass_endpoint_ratio_checks': len(ratios), 'minimum_nonK_gap_over_denominator': H,
        'minimum_ratio_controls': [{'index': i, 'carrier_index': j, 'carrier': allocated.CARRIERS[j],
                                   'endpoint': endpoint} for i, j, endpoint in controls],
        'continuum_domain': {'source_escape': '0<=sigma=1-qK<=1', 'decrement': '0<=h<=decrement_capacity',
                             'actual_residual': 'rho=S-sum_c pi_c*D_c(theta)>=0'},
        'true_function_jensen_bridge': 'Phi(K0-h)>=sum_vc Lambda_v*pi_c*(g_vc-h*(q*D_c(v)+M_lower_vc))+(A-q*h)*rho',
        'layered_bound': '-h*eK*qK+(gamma1-h*eJ)*qJ+(gamma2-h*eB)*(1-qK-qJ)+(A-q*h)*rho',
        'joint_envelope': 'Phi(K0-h)>=gamma2*sigma-(gamma2-gamma1)*sigma^2-h*(c0+c1*sigma+c2*sigma^2)+(A-q*h)*rho',
        'joint_payment_polynomial': {'constant': c0, 'linear': c1, 'quadratic': c2},
        'capacity_polynomial_factorization': '(1-sigma)*((gamma2-H*eB)*sigma-H*eK)',
        'capacity_lower_root': transition, 'far_interval': (F(1, 2), F(1)),
        'far_endpoint_margins_at_capacity': (far_half, far_one),
        'scope': 'Ordinary complete actual-source theorem with the original positive coefficients reweighted before Jensen. Every allocated M is freshly reconstructed and matches the original53 conditional digest used by71. No independent lower denominator is subtracted from a gap lower bound. The payment polynomial is part of a joint signed estimate, not an actual denominator upper bound. Original carriers, independent labels and full tails remain. No joined complete global bound, actual attainment, Lean verification or unrestricted Erdos7 resolution is claimed.'})


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
                'Exact original-source joint gap/denominator certificate')
    print('PASS: original53 survival margins, original71 gaps and joint denominator; h='
          +str(float(F(result['decrement_capacity'])))+'.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
