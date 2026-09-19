#!/usr/bin/env python3
"""Verify an actual survival-hinge deficit and all downstream target margins.

Python3.9+ standard library. Default and --check are read-only; --write
regenerates this certificate. Reconstructs the complete profile39 inputs and
consumer, then the new signed survival cost. Direct dependency pins are checked;
the computation does not replay every mathematical ancestor.
"""
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232'
PREVIOUS = 'certificates/source_norms/shared_source_deficits.json'
PREVIOUS_PIN = 'bd47e5157698faaaed4ddfb5fadf93f51dc11c69fe89e15a3a74e14117445588'
PREVIOUS_VERIFIER = 'frontier/verify_shared_source_deficits.py'
PREVIOUS_VERIFIER_PIN = '01accc355e7fc50ee313b08c948874d83252fabcdd08f6dfd4ff533f6f440d5e'
LOCAL_PINS = {
    'frontier/survival_hinge_deficit.py': '86b6d9b1e542f14b9d7b107f036767455b9db75a43607e9f9e054519a8dbb70a',
    'frontier/survival_hinge_consumer.py': '9717f3197c0dbe8b8d31e935cfb238eba0ebc0599b5792bfb6bfab1d2dbc3bc7',
}
CERTIFICATE = 'certificates/source_norms/survival_hinge_deficit.json'


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
    base = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == IO_PIN, 'Certificate IO pin')
    io = module('survival_hinge_io', base/'certificate_io.py')
    raw = io.read_artifact_bytes(base/PREVIOUS)
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Complete logical profile39 predecessor pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((base/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Profile39 verifier source pin')
    pins = previous['source_sha256'] | previous['helper_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin, 'Predecessor direct source pin: '+name)
    for name, pin in LOCAL_PINS.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Current source pin: '+name)

    def read(name):
        return json.loads(io.read_artifact_bytes(base/name), object_pairs_hook=unique)

    def load(name, path):
        return module('survival_hinge_'+name, base/path)

    source = load('math', 'verify_joint_frontier.py')
    fixed = load('fixed', 'frontier/fixed_cost.py')
    layout = load('layout', 'frontier/layout_gap.py')
    ap = load('ap', 'frontier/ap_schedule.py')
    core = load('core', 'frontier/ap_schedule_core.py')
    kc = load('kc', 'verify_killed_core_continuity.py')
    old = load('old', 'frontier/retained_five_tests.py')
    profiles = load('profiles', 'frontier/shared_source_deficits.py')
    linear = load('linear', 'frontier/shared_linear_refinement.py')
    square = load('square', 'frontier/shared_square_barrier.py')
    old_consumer = load('previous_consumer', 'frontier/shared_source_consumer.py')
    helper = load('deficit', 'frontier/survival_hinge_deficit.py')
    consumer = load('consumer', 'frontier/survival_hinge_consumer.py')
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    quadratic = read('certificates/source_norms/retained_quadratic_tests.json')
    pure = read('certificates/pure_root_profile_certificate.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    quadratic_inputs = read('certificates/source_norms/retained_quadratic_inputs.json')

    def progress(done, total):
        if done % 216 == 0 or done == total:
            print('Reconstructed predecessor profiles at '+str(done)+'/'+str(total), flush=True)

    rows, statistics = profiles.aggregate(source, fixed, layout, ap, parent, quadratic,
                                         quadratic_inputs, ap_inputs, progress)
    rows, linear_stats = linear.refine(source, fixed, ap, ap_inputs, rows)
    rows, square_stats = square.refine(source, fixed, rows, statistics['quadratic_tail_weight'])
    require(profiles.encode(statistics) == previous['source_profiles']
            and profiles.encode(linear_stats) == previous['linear_refinement']
            and profiles.encode(square_stats) == previous['square_barrier_refinement'],
            'Complete published predecessor source profiles and both refinements')
    row_hash = sha256(json.dumps(profiles.encode(rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(row_hash == previous['source_profile_sha256'], 'Every published predecessor vertex row')
    prior = old_consumer.consumer(source, core, kc, old, parent, quadratic, pure, rows,
                                   square_stats['source_barrier'], linear_stats['H41_increase'])
    require(all(profiles.encode(value) == previous[key] for key, value in prior.items() if key != 'scope'),
            'Every published profile39 consumer field, fallback and complete-core output')
    rows, deficit = helper.reconstruct(source, linear, rows)
    result = consumer.consume(source, core, kc, profiles.encode, previous, pure, rows)
    result = profiles.encode({'schema': 'erdos7-survival-hinge-deficit-v1', **result,
                              'survival_hinge': deficit,
                              'predecessor_source_profiles': statistics,
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
                json.dumps(result, sort_keys=True, separators=(',', ':')), 'Complete survival-hinge reconstruction')
    print('PASS: predecessor, 129600 survival margins, 6480 final targets, eight fallbacks and two complete cores.')
    print('Ordinary inequalities with exact rational verification; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
