#!/usr/bin/env python3
"""Reconstruct complete cell-cost absorption and its actual-law consumer.

Python3.9+ standard library. Default and --check are read-only; --write
regenerates the certificate. Reconstructs published profiles39,41 and42 before
evaluating the full absorbed cell-cost operators. Direct dependency pins are checked;
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
PREVIOUS = 'certificates/source_norms/moments-survival/absorbed_survival_hinges.json'
PREVIOUS_PIN = '51f51e59123004239e7315b2d94e36a482da5334df1f49639d039a7be31f4fc3'
PREVIOUS_VERIFIER = 'frontier/moments-survival/verify_absorbed_survival_hinges.py'
PREVIOUS_VERIFIER_PIN = 'c5170c0e3597ef83b0fb242be1e3c81ca0f93549d6d5bfb348be843c96c5c1a8'
LOCAL_PINS = {
    'frontier/moments-survival/full_absorbed_survival_hinges.py': '3c5b0ba6df9c11bbba8a9b1a31824b504072e4659a2f0a9aa8348a0fe9e8e79d',
    'frontier/moments-survival/full_absorbed_survival_consumer.py': '29dd25c3d3b4216b69f2a6bf597ec4fbbbcd41146c1ba0248a18e8ff515b1935',
}
CERTIFICATE = 'certificates/source_norms/moments-survival/full_absorbed_survival_hinges.json'


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
    io = module('full_absorbed_hinge_io', base/'certificate_io.py')
    raw = io.read_artifact_bytes(base/PREVIOUS)
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Complete logical profile42 predecessor pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((base/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Profile42 verifier source pin')
    pins = previous['source_sha256'] | previous['helper_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin,
                'Predecessor direct source pin: '+name)
    require(set(LOCAL_PINS) == {'frontier/moments-survival/full_absorbed_survival_hinges.py',
                               'frontier/moments-survival/full_absorbed_survival_consumer.py'}, 'Complete current helper pins')
    for name, pin in LOCAL_PINS.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Current source pin: '+name)

    def read(name):
        return json.loads(io.read_artifact_bytes(base/name), object_pairs_hook=unique)

    def load(name, path):
        return module('full_absorbed_hinge_'+name, base/path)

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
    absorption42 = load('absorption42', 'frontier/moments-survival/absorbed_survival_hinges.py')
    consumer42 = load('consumer42', 'frontier/moments-survival/absorbed_survival_consumer.py')
    helper = load('absorption', 'frontier/moments-survival/full_absorbed_survival_hinges.py')
    consumer = load('consumer', 'frontier/moments-survival/full_absorbed_survival_consumer.py')
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    quadratic = read('certificates/source_norms/retained-transport/retained_quadratic_tests.json')
    pure = read('certificates/pure_root_profile_certificate.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    quadratic_inputs = read('certificates/source_norms/retained-transport/retained_quadratic_inputs.json')
    previous39 = read('certificates/source_norms/source-budgets/shared_source_deficits.json')
    previous41 = read('certificates/source_norms/moments-survival/survival_hinge_deficit.json')

    def progress(done, total):
        if done % 216 == 0 or done == total:
            print('Reconstructed predecessor profiles at '+str(done)+'/'+str(total), flush=True)

    rows, statistics = profiles.aggregate(source, fixed, layout, ap, parent, quadratic,
                                         quadratic_inputs, ap_inputs, progress)
    rows, linear_stats = linear.refine(source, fixed, ap, ap_inputs, rows)
    rows, square_stats = square.refine(source, fixed, rows, statistics['quadratic_tail_weight'])
    require(profiles.encode(statistics) == previous39['source_profiles']
            and profiles.encode(statistics) == previous41['predecessor_source_profiles']
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
    require(profiles.encode(deficit25) == previous41['survival_hinge'],
            'Every published profile41 survival margin and complete-tail identity')
    prior41 = consumer41.consume(source, core, kc, profiles.encode, previous39, pure, rows)
    require(all(profiles.encode(value) == previous41[key]
                for key, value in prior41.items() if key != 'scope'),
            'Every profile41 consumer field, fallback and complete-core output')
    rows, stats42 = absorption42.reconstruct(source, rows)
    require(profiles.encode(stats42) == previous['absorbed_hinges'],
            'Every published profile42 epsilon comparison and original-layout controller')
    prior42 = consumer42.consume(source, core, kc, profiles.encode, previous41, pure, rows)
    require(all(profiles.encode(value) == previous[key]
                for key, value in prior42.items() if key != 'scope'),
            'Every profile42 consumer field, signed endpoint, fallback and core output')
    rows, absorption = helper.reconstruct(source, rows)
    result = consumer.consume(source, core, kc, profiles.encode, previous, pure, rows)
    result = profiles.encode({'schema': 'erdos7-full-absorbed-survival-hinges-v1', **result,
                              'full_absorbed_hinges': absorption,
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
                json.dumps(result, sort_keys=True, separators=(',', ':')), 'Complete full-cell-cost absorption reconstruction')
    print('PASS: profiles39/41/42, 2592 full margins and scalar reconstructions, all final endpoints, eight fallbacks and two cores.')
    print('Ordinary inequalities with exact rational verification; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
