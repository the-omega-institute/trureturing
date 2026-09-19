#!/usr/bin/env python3
"""Verify24 frontier refinements for full linear and quadratic carrier functions.

Python3.9+ standard library. Reconstruct the complete39 source,46 survival
and47 linear lower bounds. Refine24 vertices for all41 linear and five
quadratic costs; keep47 lower bounds elsewhere. Reconstruct old47 targets
inside the new consumer, separating linear and additional quadratic gains.
Default/--check reads; --output writes standalone JSON; --write emits the
canonical certificate through the existing certificate writer.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232'
PREVIOUS = 'certificates/source_norms/joint_linear_carriers.json'
PREVIOUS_PIN = '3c1ccbe0a79dfe5c3b01424b1fd615999a162b5b7df2451936f554b3517a2385'
PREVIOUS_VERIFIER = 'frontier/verify_joint_linear_carriers.py'
PREVIOUS_VERIFIER_PIN = 'b1a460bee98749567e55e6a554286405a78a5faf2793ee09e88efdd60c1954e6'
SATURATION = 'frontier/source_barrier_saturation.py'
SATURATION_PIN = '92076ee71a6be16655bbe5c2ac223db6502da1ab5c3553a7f83bb555dbbb8363'
HELPER = 'frontier/full_linear_carrier_frontier.py'
HELPER_PIN = '98cbec50d807ed9208504c8cd2384659a4300d6909d54414e5e2156285298888'
CERTIFICATE = 'certificates/source_norms/full_linear_carrier_frontier.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


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


def main():
    base = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--output', type=Path)
    args = parser.parse_args()
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == IO_PIN, 'Certificate IO pin')
    io = module('joint_linear_io', base/'certificate_io.py')
    raw = io.read_artifact_bytes(base/PREVIOUS)
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Logical profile47 certificate pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['schema'] == 'erdos7-joint-linear-carriers-v1'
            and previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((base/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Published47 verifier identity')
    pins = previous['source_sha256'] | previous['helper_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin,
                'Inherited source or logical certificate pin: '+name)
    for name, pin in ((HELPER, HELPER_PIN), (SATURATION, SATURATION_PIN)):
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Current helper pin: '+name)

    def read(name):
        return json.loads(io.read_artifact_bytes(base/name), object_pairs_hook=unique)

    def load(name, path):
        return module('joint_linear_'+name, base/path)

    source = load('source', 'verify_joint_frontier.py')
    fixed = load('fixed', 'frontier/fixed_cost.py')
    layout = load('layout', 'frontier/layout_gap.py')
    ap = load('ap', 'frontier/ap_schedule.py')
    core = load('core', 'frontier/ap_schedule_core.py')
    kc = load('kc', 'verify_killed_core_continuity.py')
    profiles = load('profiles', 'frontier/shared_source_deficits.py')
    linear = load('linear', 'frontier/shared_linear_refinement.py')
    square = load('square', 'frontier/shared_square_barrier.py')
    full = load('full', 'frontier/full_absorbed_survival_hinges.py')
    survival = load('survival', 'frontier/joint_survival_carriers.py')
    saturation = load('saturation', SATURATION)
    six = load('six', 'frontier/joint_linear_carriers.py')
    helper = load('helper', HELPER)
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    quadratic = read('certificates/source_norms/retained_quadratic_tests.json')
    pure = read('certificates/pure_root_profile_certificate.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    quadratic_inputs = read('certificates/source_norms/retained_quadratic_inputs.json')
    previous39 = read('certificates/source_norms/shared_source_deficits.json')
    previous41 = read('certificates/source_norms/survival_hinge_deficit.json')
    previous43 = read('certificates/source_norms/full_absorbed_survival_hinges.json')
    previous46 = read('certificates/source_norms/joint_survival_carriers.json')

    def progress(label):
        def update(done, total):
            if done % 216 == 0:
                print(label+' '+str(done)+'/'+str(total), flush=True)
        return update

    rows, source_stats = profiles.aggregate(source, fixed, layout, ap, parent, quadratic,
                                            quadratic_inputs, ap_inputs, progress('Reconstructed source'))
    rows, linear_stats = linear.refine(source, fixed, ap, ap_inputs, rows)
    rows, square_stats = square.refine(source, fixed, rows, source_stats['quadratic_tail_weight'])
    require(profiles.encode(source_stats) == previous39['source_profiles']
            and profiles.encode(source_stats) == previous41['predecessor_source_profiles']
            and profiles.encode(linear_stats) == previous39['linear_refinement']
            and profiles.encode(square_stats) == previous39['square_barrier_refinement'],
            'Complete published source and refinement statistics')
    row_hash = sha256(json.dumps(profiles.encode(rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(row_hash == previous39['source_profile_sha256'] == previous['predecessor_source_profile_sha256'],
            'Complete reconstructed39 source digest')
    rows, survival_stats = survival.reconstruct(source, linear, full, previous41, previous43, rows)
    published_survival = dict(previous46['joint_survival'])
    published_survival['rows'] = [row for first in published_survival.pop('row_blocks')
                                 for second in first for row in second]
    require(profiles.encode(survival_stats) == published_survival, 'All published46 conditioned survival values')
    experiment = saturation.Experiment(base)
    rows, six_statistics = six.reconstruct(experiment, rows, progress('Reconstructed six linear tests'))
    published_six = dict(previous['six_linear'])
    published_six['rows'] = [row for first in published_six.pop('row_blocks')
                            for second in first for row in second]
    require(profiles.encode(six_statistics) == published_six, 'All published47 conditioned linear values')
    rows, statistics = helper.reconstruct(experiment, previous, rows, progress('Refined frontier'))
    result = helper.consume(source, core, kc, previous, pure, rows)
    conditional = statistics.pop('rows')
    require(len(conditional) == 24, 'Exactly24 individually refined frontier rows')
    blocks = [conditional[start:start+12] for start in range(0, len(conditional), 12)]
    statistics['row_blocks'] = blocks
    result = profiles.encode({'schema': 'erdos7-full-linear-carrier-frontier-v1', **result,
                              'frontier': statistics, 'predecessor_source_profile_sha256': row_hash,
                              'predecessor_survival_conditional_sha256': survival_stats['conditional_margin_sha256'],
                              'predecessor_linear_conditional_sha256': six_statistics['conditional_margin_sha256'],
                              'source_sha256': pins | {'certificate_io.py': IO_PIN, PREVIOUS: PREVIOUS_PIN,
                                                        PREVIOUS_VERIFIER: PREVIOUS_VERIFIER_PIN},
                              'helper_sha256': {HELPER: HELPER_PIN, SATURATION: SATURATION_PIN},
                              'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()})
    rendered = json.dumps(result, indent=2)+'\n'
    if args.output is not None:
        args.output.write_text(rendered)
    elif args.write:
        io.write_certificate_text(base/CERTIFICATE, rendered)
    else:
        actual = read(CERTIFICATE)
        require(json.dumps(actual, sort_keys=True, separators=(',', ':')) ==
                json.dumps(result, sort_keys=True, separators=(',', ':')), 'Full41-linear/five-quadratic frontier reconstruction')
    print('PASS: complete39/46/47 source reconstruction;24 true41-linear/five-quadratic refinements,1272 inherited lower bounds, both gain stages, all signed endpoints, eight fallbacks and two complete cores.')
    print('Ordinary proof with exact rational arithmetic; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
