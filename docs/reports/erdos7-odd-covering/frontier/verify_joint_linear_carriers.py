#!/usr/bin/env python3
"""Verify six original linear tests sharing the survival-carrier mixture.

Python3.9+ standard library. Reconstruct the complete profile39 source, then
all profile46 conditional survival rows, then the six conditioned linear
margins and the new consumer. Old consumers are not replayed. Independent-six
improvement is separated from the additional common-carrier improvement.
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
PREVIOUS = 'certificates/source_norms/joint_survival_carriers.json'
PREVIOUS_PIN = '9b8b6f5bfabed669cea810b759d2d02f19e47cce1999851dcd031cfa77115a72'
PREVIOUS_VERIFIER = 'frontier/verify_joint_survival_carriers.py'
PREVIOUS_VERIFIER_PIN = '778b5a597d57b8aef9ed8e7ba68b74c0b17d90729f87ed8dd36fb8f9ee8ae6f9'
SATURATION = 'frontier/source_barrier_saturation.py'
SATURATION_PIN = '92076ee71a6be16655bbe5c2ac223db6502da1ab5c3553a7f83bb555dbbb8363'
HELPER = 'frontier/joint_linear_carriers.py'
HELPER_PIN = '1bb9e5dac83371f90a1270eb8f4a3e9fcee38b3f373ecef8becf1da6f994ed64'
CERTIFICATE = 'certificates/source_norms/joint_linear_carriers.json'


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
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Logical profile46 certificate pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['schema'] == 'erdos7-joint-survival-carriers-v1'
            and previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((base/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Published46 verifier identity')
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
    helper = load('helper', HELPER)
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    quadratic = read('certificates/source_norms/retained_quadratic_tests.json')
    pure = read('certificates/pure_root_profile_certificate.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    quadratic_inputs = read('certificates/source_norms/retained_quadratic_inputs.json')
    previous39 = read('certificates/source_norms/shared_source_deficits.json')
    previous41 = read('certificates/source_norms/survival_hinge_deficit.json')
    previous43 = read('certificates/source_norms/full_absorbed_survival_hinges.json')

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
    published_survival = dict(previous['joint_survival'])
    published_survival['rows'] = [row for first in published_survival.pop('row_blocks')
                                 for second in first for row in second]
    require(profiles.encode(survival_stats) == published_survival, 'All published46 conditioned survival values')
    experiment = saturation.Experiment(base)
    rows, statistics = helper.reconstruct(experiment, rows, progress('Conditioned six linear tests'))
    result = helper.consume(source, core, kc, previous, pure, rows)
    conditional = statistics.pop('rows')
    require(len(conditional) == 1296, 'Complete conditioned linear source rows')
    blocks = [conditional[start:start+12] for start in range(0, len(conditional), 12)]
    statistics['row_blocks'] = [blocks[start:start+6] for start in range(0, len(blocks), 6)]
    result = profiles.encode({'schema': 'erdos7-joint-linear-carriers-v1', **result,
                              'six_linear': statistics, 'predecessor_source_profile_sha256': row_hash,
                              'predecessor_survival_conditional_sha256': survival_stats['conditional_margin_sha256'],
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
                json.dumps(result, sort_keys=True, separators=(',', ':')), 'Full six-linear-carrier reconstruction')
    print('PASS: complete39 source and46 survival reconstruction; six independent original tests, common18 carriers, both gain components, all signed endpoints, eight fallbacks and two complete cores.')
    print('Ordinary proof with exact rational arithmetic; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
