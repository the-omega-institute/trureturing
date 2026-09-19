#!/usr/bin/env python3
"""Reconstruct whole-hinge absorption and its complete actual-law consumer.

Python3.9+ standard library. Default and --check are read-only; --write
regenerates the certificate. Reconstructs published profiles39 and41 before
adding the two absorbed hinge bounds. Direct dependency pins are checked;
this does not replay every mathematical ancestor or verify a Lean theorem.
"""
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2'
PREVIOUS = 'certificates/source_norms/moments-survival/survival_hinge_deficit.json'
PREVIOUS_PIN = '484ee018b5f7fee564317a37975fabb5d5ae7e8046fce0c88714209af67145c0'
PREVIOUS_VERIFIER = 'frontier/moments-survival/verify_survival_hinge_deficit.py'
PREVIOUS_VERIFIER_PIN = '6159205f227d913376f35c223a0be07d5b7fc0a79732bac04f68564ff95bca16'
LOCAL_PINS = {
    'frontier/moments-survival/absorbed_survival_hinges.py': '03b4d8d9c80470946ce4bfd44cd40a07c241f6c22058952fc59b88c71e1d7e10',
    'frontier/moments-survival/absorbed_survival_consumer.py': 'd47a9e4ccaec3d277899830f92aaaf1e9cc736bb628165aa6547c3521a8f9f53',
}
CERTIFICATE = 'certificates/source_norms/moments-survival/absorbed_survival_hinges.json'


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
    base = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == IO_PIN, 'Certificate IO pin')
    io = module('absorbed_hinge_io', base/'certificate_io.py')
    raw = io.read_artifact_bytes(base/PREVIOUS)
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Complete logical profile41 predecessor pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((base/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Profile41 verifier source pin')
    pins = previous['source_sha256'] | previous['helper_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin,
                'Predecessor direct source pin: '+name)
    require(set(LOCAL_PINS) == {'frontier/moments-survival/absorbed_survival_hinges.py',
                               'frontier/moments-survival/absorbed_survival_consumer.py'}, 'Complete current helper pins')
    for name, pin in LOCAL_PINS.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Current source pin: '+name)

    def read(name):
        return json.loads(io.read_artifact_bytes(base/name), object_pairs_hook=unique)

    def load(name, path):
        return module('absorbed_hinge_'+name, base/path)

    source = load('math', 'verify_joint_frontier.py')
    fixed = load('fixed', 'frontier/comparison-bounds/fixed_cost.py')
    layout = load('layout', 'frontier/cover-geometry/layout_gap.py')
    ap = load('ap', 'frontier/cover-geometry/ap_schedule.py')
    core = load('core', 'frontier/cover-geometry/ap_schedule_core.py')
    kc = load('kc', 'verify_killed_core_continuity.py')
    old = load('old', 'frontier/retained-transport/retained_five_tests.py')
    profiles = load('profiles', 'frontier/source-budgets/shared_source_deficits.py')
    linear = load('linear', 'frontier/source-budgets/shared_linear_refinement.py')
    square = load('square', 'frontier/source-budgets/shared_square_barrier.py')
    consumer39 = load('consumer39', 'frontier/source-budgets/shared_source_consumer.py')
    hinge25 = load('hinge25', 'frontier/moments-survival/survival_hinge_deficit.py')
    consumer41 = load('consumer41', 'frontier/moments-survival/survival_hinge_consumer.py')
    helper = load('absorption', 'frontier/moments-survival/absorbed_survival_hinges.py')
    consumer = load('consumer', 'frontier/moments-survival/absorbed_survival_consumer.py')
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    quadratic = read('certificates/source_norms/retained-transport/retained_quadratic_tests.json')
    pure = read('certificates/pure_root_profile_certificate.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    quadratic_inputs = read('certificates/source_norms/retained-transport/retained_quadratic_inputs.json')
    previous39 = read('certificates/source_norms/source-budgets/shared_source_deficits.json')

    def progress(done, total):
        if done % 216 == 0 or done == total:
            print('Reconstructed predecessor profiles at '+str(done)+'/'+str(total), flush=True)

    rows, statistics = profiles.aggregate(source, fixed, layout, ap, parent, quadratic,
                                         quadratic_inputs, ap_inputs, progress)
    rows, linear_stats = linear.refine(source, fixed, ap, ap_inputs, rows)
    rows, square_stats = square.refine(source, fixed, rows, statistics['quadratic_tail_weight'])
    require(profiles.encode(statistics) == previous39['source_profiles']
            and profiles.encode(statistics) == previous['predecessor_source_profiles']
            and profiles.encode(linear_stats) == previous39['linear_refinement']
            and profiles.encode(square_stats) == previous39['square_barrier_refinement'],
            'Complete published predecessor source profiles and refinements')
    row_hash = sha256(json.dumps(profiles.encode(rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(row_hash == previous39['source_profile_sha256'], 'Every published profile39 vertex row')
    prior39 = consumer39.consumer(source, core, kc, old, parent, quadratic, pure, rows,
                                  square_stats['source_barrier'], linear_stats['H41_increase'])
    require(all(profiles.encode(value) == previous39[key]
                for key, value in prior39.items() if key != 'scope'),
            'Every profile39 consumer field, fallback and complete-core output')
    rows, deficit25 = hinge25.reconstruct(source, linear, rows)
    require(profiles.encode(deficit25) == previous['survival_hinge'],
            'Every published profile41 survival margin and complete-tail identity')
    prior41 = consumer41.consume(source, core, kc, profiles.encode, previous39, pure, rows)
    require(all(profiles.encode(value) == previous[key]
                for key, value in prior41.items() if key != 'scope'),
            'Every profile41 consumer field, fallback and complete-core output')
    rows, absorption = helper.reconstruct(source, rows)
    result = consumer.consume(source, core, kc, profiles.encode, previous, pure, rows)
    result = profiles.encode({'schema': 'erdos7-absorbed-survival-hinges-v1', **result,
                              'absorbed_hinges': absorption,
                              'source_sha256': pins | {'certificate_io.py': IO_PIN, PREVIOUS: PREVIOUS_PIN,
                                                        PREVIOUS_VERIFIER: PREVIOUS_VERIFIER_PIN},
                              'helper_sha256': LOCAL_PINS,
                              'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()})
    path = base/CERTIFICATE
    if args.write:
        io.write_certificate_text(path, json.dumps(result, indent=2)+'\n')
    else:
        actual = json.loads(io.read_artifact_bytes(path), object_pairs_hook=unique)
        require(json.dumps(actual, sort_keys=True, separators=(',', ':')) ==
                json.dumps(result, sort_keys=True, separators=(',', ':')), 'Complete absorbed-hinge reconstruction')
    print('PASS: profiles39/41, 259200 absorption comparisons, 6480 final targets, eight fallbacks and two cores.')
    print('Ordinary inequalities with exact rational verification; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
