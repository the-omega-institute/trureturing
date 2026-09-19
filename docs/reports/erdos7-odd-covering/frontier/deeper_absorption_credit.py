#!/usr/bin/env python3
"""Consume the uniform27/81 absorption credit without another vertex scan.

Python3.9+ standard library. Default is read-only; --output writes exact JSON.
The numerical improvement uses the ordinary same-law four-cofactor credit and
an actual-mass rescaling. It is a conservative bound, not the exact optimum
of a refined source envelope or a certificate for every relaxed endpoint.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
PREVIOUS = 'certificates/source_norms/full_absorbed_survival_hinges.json'
PURE = 'certificates/pure_root_profile_certificate.json'
PINS = {
    'certificate_io.py': '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232',
    'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe',
    'frontier/ap_schedule_core.py': '365b6c1f9a70dff5378a7d3a73a06879ee6193fbc69a4ac68ecfed1972e95617',
    'verify_killed_core_continuity.py': '4dc984fd1f8554a4938b59f1fd74ec8851833c4d3b43f329b7cc306c9ad7c19e',
    PREVIOUS: '3b9ac3f0a8ce3b5e11c5f32165c713cd8307f7bf09f0d49426a5f719a18fcef7',
    PURE: 'b1ba6c871d993fd43152351c2b823a7955d93ce4500fbe29f9420c38f7f72196',
}
CAPS = ((11, F(5, 3)), (13, F(12, 7)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def encode(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): encode(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [encode(v) for v in value]
    return value


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: '+key)
        result[key] = value
    return result


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: '+str(path))
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def calculate(base):
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == PINS['certificate_io.py'],
            'Certificate IO source SHA256')
    io = module('deeper_credit_io', base/'certificate_io.py')
    for name, pin in PINS.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin,
                'Direct source or logical certificate SHA256: '+name)
    source = module('deeper_credit_source', base/'verify_joint_frontier.py')
    core = module('deeper_credit_core', base/'frontier/ap_schedule_core.py')
    kc = module('deeper_credit_kc', base/'verify_killed_core_continuity.py')
    previous = json.loads(io.read_artifact_bytes(base/PREVIOUS), object_pairs_hook=unique)
    pure = json.loads(io.read_artifact_bytes(base/PURE), object_pairs_hook=unique)
    require(previous['schema'] == 'erdos7-full-absorbed-survival-hinges-v1'
            and F(previous['q_effective']) == F(23, 42)
            and F(previous['source_G357']) == F(102715, 2916),
            'Same predecessor law, charged survival coefficient and source norm')
    # Actual main-branch cells have n_l<=eta_l<=1/9. This universal bound,
    # not a relaxed-vertex assertion, is the mathematical rescaling input.
    mass_upper = F(5, 9)
    require(len(source.ROOT) == 5 and mass_upper == F(len(source.ROOT), 9),
            'Five surviving mod9 cells in the actual source branch')
    depth_mass = F(1, 27)+F(1, 81)
    hinge_credits = {t: F(1, 5**t)*depth_mass/5 for t in (4, 5)}
    delta = hinge_credits[4]/6+F(4, 33)*hinge_credits[5]
    require(hinge_credits == {4: F(4, 253125), 5: F(4, 1265625)}
            and delta == F(14, 4640625) > 0,
            'Exact ordinary27/81 same-law raw denominator credit')
    credit = delta/mass_upper
    factor = 1-credit
    require(credit == F(14, 2578125) and factor == F(2578111, 2578125)
            and 0 < factor < 1, 'Positive conservative actual-mass rescaling')
    constants = {'bound': source.WHOLE_CONST, 'Gamma13': F(16),
                 'T13_81': F(0), 'combined': source.WHOLE_CONST}
    targets = {}
    for key, constant in constants.items():
        old = F(previous[key])
        require(old > constant, 'Positive old fixed-target numerator multiplier: '+key)
        targets[key] = constant+(old-constant)*factor
        require(constant < targets[key] < old, 'Strict conservative actual-law improvement: '+key)
    rho = F(previous['rho'])+credit
    require(0 < F(previous['rho']) < rho <= 1, 'Strict actual survival improvement')
    branches, full_rho = core.fallbacks(source, CAPS, F(previous['source_G357']),
        {key: targets[key] for key in constants if key != 'combined'}, rho)
    require(full_rho == rho and len(branches) == 8,
            'All unchanged fallback branches preserve the improved survival target')
    for branch in branches:
        branch['combined_bound'] = branch['bound']+branch['T13_81']
        branch['combined_margin'] = targets['combined']-branch['combined_bound']
        require(branch['combined_margin'] > 0, 'Every complete fallback combined bound')
    inputs, errors = core.core_errors(kc, pure['source_inputs'], targets['Gamma13'], rho,
                                     targets['T13_81'], targets['bound'])
    combined_gain = targets['bound']+targets['T13_81']-targets['combined']
    require(combined_gain == factor*F(previous['combined_target_gain']) >= 0,
            'Inherited common-law sum improvement under the same affine rescaling')
    require(len(errors) == 2, 'Both complete core interfaces')
    for error in errors:
        error['combined_gap'] = targets['combined']+error['total']-403
        require(error['combined_gap'] == error['gap']-combined_gain,
                'Combined target uses the same complete-core error')
    return {'schema': 'erdos7-deeper-absorption-credit-v1', **targets, 'rho': rho,
            'q_effective': F(previous['q_effective']), 'hinge_credits': hinge_credits,
            'raw_denominator_credit': delta, 'actual_source_mass_upper': mass_upper,
            'uniform_normalized_credit': credit, 'rescaling_factor': factor,
            'predecessor_targets': {key: F(previous[key]) for key in constants},
            'predecessor_rho': F(previous['rho']),
            'target_improvements': {key: F(previous[key])-targets[key] for key in constants},
            'survival_improvement': credit, 'combined_target_gain': combined_gain,
            'source_inputs': inputs, 'fallbacks': branches, 'core_errors': errors,
            'source_G357': F(previous['source_G357']), 'input_sha256': PINS,
            'fallback_checks': 8, 'complete_core_checks': 2,
            'new_source_vertex_evaluations': 0,
            'scope': 'Conditional on the ordinary uniform27/81 credit on the same actual law, Delta_new=Delta43+delta<=rho_actual*S<=S<=5/9. Old fixed-target inequalities give the displayed conservative rescaling. This is not a new relaxed-domain endpoint scan, not an exact four-cofactor envelope optimum, and not an unrestricted Erdos7 solution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate(Path(__file__).resolve().parents[1])
    rendered = json.dumps(encode(result), indent=2)+'\n'
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end='')


if __name__ == '__main__':
    main()
