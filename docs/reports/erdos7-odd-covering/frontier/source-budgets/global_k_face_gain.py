#!/usr/bin/env python3
"""Exact global K improvement from whole-face identity-cost neighborhoods.

The ordinary proof applies old separate concavity, product concentration,
actual mass slack, and a pointwise local replacement. This checker verifies
the complete rational reserve, target decrement, and all eight fallbacks.
"""
import argparse
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
CERTIFICATE = 'certificates/source_norms/source-budgets/global_k_face_gain.json'
PINS = {
    'certificate_io.py': '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2',
    'frontier/source-budgets/global_control_faces.py': '1558ad83f42b2879336445ab80c4d525df58560734cc45f8bcbbbb0a3ece9c35',
    'certificates/source_norms/source-budgets/global_control_faces.json': 'f2843dc163436de4f24291e5f311f3904e38272707b44bc9516ef2afc207e4f1',
    'frontier/endpoint-bounds/endpoint_k_face_neighborhood.py': '75577c2050d77c48f3cce7640534a7021e4f9e1a12bd7e22386022262b233728',
    'certificates/source_norms/endpoint-bounds/endpoint_k_face_neighborhood.json': '35aaced8b84aa75f80f5ec22935bb51cbf1395bdba0e38d6378af0ce2aaf1353',
    'certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json': 'ec6c4cf8b2c2f53179eead3d0a7499ca69fb796d57df6b65a91b0d672745a1b5',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module: '+str(path))
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
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'], 'Pinned IO')
    io = module('global_k_io', base/'certificate_io.py')
    read = lambda path: json.loads(io.read_artifact_bytes(base/path))
    for path, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Pinned input: '+path)
    old = read('certificates/source_norms/comparison-bounds/allocated_seven_thresholds.json')
    faces = read('certificates/source_norms/source-budgets/global_control_faces.json')
    local = read('certificates/source_norms/endpoint-bounds/endpoint_k_face_neighborhood.json')
    used = dict(PINS)
    for document in (old, faces, local):
        for path, pin in document['source_sha256'].items():
            require(path not in used or used[path] == pin, 'Consistent input pins: '+path)
            require(sha256(io.read_artifact_bytes(base/path)).hexdigest() == pin, 'Inherited input: '+path)
            used[path] = pin
    source = module('global_k_source', base/'verify_joint_frontier.py')
    schedule = module('global_k_schedule', base/'frontier/cover-geometry/ap_schedule.py')
    fixed = module('global_k_fixed', base/'frontier/comparison-bounds/fixed_cost.py')
    prior49 = read('certificates/source_norms/source-budgets/full_linear_carrier_frontier.json')
    specs, groups, _ = schedule.inventory(source, fixed, read('certificates/ap_schedule_norms.json'))
    require(len(specs) == 46 and specs[40]['tag'] == ('h', F(0)), 'Live identity direction40')
    weights = {'R17': F(1), 'R19': source.P17, 'R5': source.EXTRA5}
    beta = sum(weights[g['name']]*g['tail_coefficient'] for g in groups)
    require(beta == F(94212612766226, 1174116234095805) > 0, 'Complete positive identity coefficient')
    for group in prior49['frontier']['row_blocks']:
        for row in group:
            direction = row['linear_directions'][40]
            require(direction['index'] == 40 and direction['name'] == 'linear'
                and F(direction['constant']) == 6 and F(direction['weight']) == beta,
                'Every refined row has the same live identity coefficient')

    K0, q = F(old['combined']), F(old['q_effective'])
    slope = source.AC*F(old['H16'])+F(old['H41'])+F(old['A81'])
    a = q*(K0-source.WHOLE_CONST)-slope
    require(a == F(old['coefficients']['combined']) == F(faces['targets']['K']['mass_coefficient']) > 0,
        'Exact common-K signed mass coefficient')
    rho = F(old['rho'])
    require(0 < rho < q < 1, 'Positive old survival comparison and its lower-mass sign')
    gamma = F(faces['targets']['K']['minimum_positive_signed_gap_lower_endpoint'])
    require(gamma == F(faces['targets']['K']['minimum_positive_signed_gap_both_endpoints']) > 0,
        'Exact next positive K gap')
    require(faces['targets']['K']['maximal_cartesian_zero_boxes'] == [
        [[1], [2], [3, 4, 5], [1], [0], [14]],
        [[2], [2], [3, 4, 5], [2], [0], [13]]], 'Both complete K faces')
    require(local['face_vertices'] == [398, 410, 422] and local['carrier'] == [1, 1]
        and local['symmetric_face_vertices'] == [616, 628, 640]
        and local['symmetric_carrier'] == [1, 0], 'Local theorem covers both global control faces')

    delta, eps0, sqrt_upper = F(1, 25000), F(1, 100000), F(1, 300)
    # These constants are the explicit product projection estimates in note71.
    eta_coefficient = F(1, 9)
    n_coefficient = (F(1)+F(5, 4)+F(3, 2)+F(1, 2))/9+F(1, 36)
    d_coefficient = F(5, 4)+F(3, 2)+F(1, 2)
    defect_coefficient = F(3, 4)+F(1, 72)
    tau_coefficient = eta_coefficient+n_coefficient+d_coefficient+defect_coefficient
    require((n_coefficient, d_coefficient, tau_coefficient) == (F(1, 2), F(13, 4), F(37, 8)),
        'Exact face-distance conversion')
    tau, kappa, xi = tau_coefficient*delta, delta, F(4, 45)*delta
    require(delta <= F(1, 18) and tau <= F(local['guards']['tau'])
        and eps0 <= F(local['guards']['epsilon']) and 0 <= xi < eps0
        and eps0 <= sqrt_upper**2, 'Whole-face guard, mass bridge, rational square-root upper bound')
    gains = {k: F(v) for k, v in local['guaranteed_gain'].items()}
    require(gains == {'constant': F(677, 24300), 'tau': F(-54), 'epsilon': F(-608),
        'kappa': F(-7, 2), 'sqrt_epsilon': F(-2)}, 'Exact pointwise live-direction gain')
    gain = gains['constant']+gains['tau']*tau+gains['epsilon']*eps0+gains['kappa']*kappa+gains['sqrt_epsilon']*sqrt_upper
    require(gain == F(121097, 24300000) > 0, 'Strict local gain on the entire chosen neighborhood')
    reserves = {'outside_faces': gamma*delta, 'actual_mass_escape': a*(eps0-xi), 'local_identity_gain': beta*gain}
    reserve = min(reserves.values())
    require(reserve == reserves['outside_faces'] > 0, 'Positive global three-case reserve')
    denominator_upper = F(5, 9)
    decrease = reserve/(2*denominator_upper)
    K1 = K0-decrease
    require(decrease == F(9, 250000)*gamma > 0 and K1 > source.WHOLE_CONST
        and a-q*decrease > 0 and reserve-decrease*denominator_upper == reserve/2,
        'Strict lower global target and unchanged sign branch')
    fallbacks = []
    for row in old['fallbacks']:
        bound = F(row['bound'])+F(row['T13_81'])
        require(bound == F(row['combined_bound']) < K1, 'Each complete fallback remains below new target')
        fallbacks.append({'branch': row['branch'], 'bound': bound, 'old_gap': K0-bound, 'new_gap': K1-bound})
    require(len(fallbacks) == 8, 'All eight source fallbacks')
    cores = []
    for row in old['core_errors']:
        error = F(row['total'])
        gap = K1+error-403
        require(K0+error-403 == F(row['combined_gap']) and gap > 0, 'Complete terminal gap remains positive')
        cores.append({'box': row['box'], 'current': row['current'], 'unchanged_error': error,
                      'old_combined_gap': F(row['combined_gap']), 'new_combined_gap': gap})
    require(len(cores) == 2, 'Both complete terminal core comparisons retained')
    return encode({'schema': 'erdos7-global-k-face-gain-v1', 'source_sha256': used,
        'old_K': K0, 'new_K': K1, 'strict_decrease': decrease, 'signed_mass_coefficient': a,
        'identity_cost_coefficient': beta, 'gamma_K': gamma,
        'face_barycentric_radius': delta, 'epsilon_cutoff': eps0, 'sqrt_epsilon_upper': sqrt_upper,
        'tau_conversion_coefficient': tau_coefficient, 'tau_upper': tau, 'kappa_upper': kappa,
        'carrier_mass_slack_upper': xi, 'local_identity_gain_lower': gain,
        'three_case_reserves': reserves, 'global_signed_reserve': reserve,
        'positive_survival_lower': rho, 'comparison_denominator_upper': denominator_upper,
        'new_mass_coefficient': a-q*decrease, 'new_signed_margin_lower': reserve/2,
        'fallbacks': fallbacks, 'minimum_fallback_gap': min(r['new_gap'] for r in fallbacks),
        'complete_cores': cores,
        'scope': 'Strict global common-law K improvement on the inherited full source split. Original independent tests, complete exponent tails, actual mass slack and all eight fallbacks retained. Ordinary proof plus rational certificate; unrestricted Erdos7 and Lean verification remain open.'})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=Path(__file__).resolve().parents[2])
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--output', type=Path)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = calculate(args.base)
    io = module('global_k_writer', args.base/'certificate_io.py')
    rendered = json.dumps(result, indent=2)+'\n'
    if args.check:
        require(json.loads(io.read_artifact_bytes(args.base/CERTIFICATE)) == result, 'Canonical global K improvement certificate')
    elif args.write:
        io.write_certificate_text(args.base/CERTIFICATE, rendered)
    elif args.output is not None:
        args.output.write_text(rendered)
    else:
        print(rendered)
    print('PASS: strict global K decrease '+result['strict_decrease']+'; all eight fallbacks; both terminal gaps remain positive.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
