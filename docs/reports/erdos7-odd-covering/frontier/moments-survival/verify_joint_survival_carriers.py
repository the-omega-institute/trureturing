#!/usr/bin/env python3
"""Verify common-carrier survival with the conditional27/81 credit.

Python3.9+ standard library. Reconstructs the complete profile39 source rows
and their digest, then the independent41/43 hinge margins and the new joint
consumer. It does not rerun old consumers or the epsilon-only42 tables.
Default and --check are read-only; --output writes standalone exact JSON,
while --write regenerates the canonical certificate through certificate IO.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2'
PREVIOUS = 'certificates/source_norms/moments-survival/full_absorbed_survival_hinges.json'
PREVIOUS_PIN = '4da2cd7261df906d0e0c431b6414196beead74233a2647e2e33e021a9d348f84'
PREVIOUS_VERIFIER = 'frontier/moments-survival/verify_full_absorbed_survival_hinges.py'
PREVIOUS_VERIFIER_PIN = 'a534b9cc2e8dea91cac97dfecf01620cb573608dfeb453ef172911ab7647cb63'
HELPER = 'frontier/moments-survival/joint_survival_carriers.py'
HELPER_PIN = '4fd5744bebf3a20ba2a62a1fc798e0278b903b4d139ae1808c62a392d419043d'
CERTIFICATE = 'certificates/source_norms/moments-survival/joint_survival_carriers.json'


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
    modes.add_argument('--check', action='store_true')
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--output', type=Path)
    args = parser.parse_args()
    require(sha256((base/'certificate_io.py').read_bytes()).hexdigest() == IO_PIN, 'Certificate IO pin')
    io = module('joint_survival_io', base/'certificate_io.py')
    raw = io.read_artifact_bytes(base/PREVIOUS)
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Logical profile43 certificate pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['schema'] == 'erdos7-full-absorbed-survival-hinges-v1'
            and previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((base/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Published43 verifier identity')
    pins = previous['source_sha256'] | previous['helper_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin,
                'Inherited direct source or logical certificate pin: '+name)
    require(sha256((base/HELPER).read_bytes()).hexdigest() == HELPER_PIN, 'Current joint helper pin')

    def read(name):
        return json.loads(io.read_artifact_bytes(base/name), object_pairs_hook=unique)

    def load(name, path):
        return module('joint_survival_'+name, base/path)

    source = load('source', 'verify_joint_frontier.py')
    fixed = load('fixed', 'frontier/comparison-bounds/fixed_cost.py')
    layout = load('layout', 'frontier/cover-geometry/layout_gap.py')
    ap = load('ap', 'frontier/cover-geometry/ap_schedule.py')
    core = load('core', 'frontier/cover-geometry/ap_schedule_core.py')
    kc = load('kc', 'verify_killed_core_continuity.py')
    profiles = load('profiles', 'frontier/source-budgets/shared_source_deficits.py')
    linear = load('linear', 'frontier/source-budgets/shared_linear_refinement.py')
    square = load('square', 'frontier/source-budgets/shared_square_barrier.py')
    full = load('full', 'frontier/moments-survival/full_absorbed_survival_hinges.py')
    helper = load('helper', HELPER)
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    quadratic = read('certificates/source_norms/retained-transport/retained_quadratic_tests.json')
    pure = read('certificates/pure_root_profile_certificate.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    quadratic_inputs = read('certificates/source_norms/retained-transport/retained_quadratic_inputs.json')
    previous39 = read('certificates/source_norms/source-budgets/shared_source_deficits.json')
    previous41 = read('certificates/source_norms/moments-survival/survival_hinge_deficit.json')

    def progress(done, total):
        if done % 216 == 0:
            print('Reconstructed source '+str(done)+'/'+str(total), flush=True)

    rows, source_stats = profiles.aggregate(source, fixed, layout, ap, parent, quadratic,
                                            quadratic_inputs, ap_inputs, progress)
    rows, linear_stats = linear.refine(source, fixed, ap, ap_inputs, rows)
    rows, square_stats = square.refine(source, fixed, rows, source_stats['quadratic_tail_weight'])
    require(profiles.encode(source_stats) == previous39['source_profiles']
            and profiles.encode(source_stats) == previous41['predecessor_source_profiles']
            and profiles.encode(linear_stats) == previous39['linear_refinement']
            and profiles.encode(square_stats) == previous39['square_barrier_refinement'],
            'All published source-profile and refinement statistics')
    row_hash = sha256(json.dumps(profiles.encode(rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(row_hash == previous39['source_profile_sha256'], 'Complete canonical39 source-row digest')
    rows, statistics = helper.reconstruct(source, linear, full, previous41, previous, rows)
    result = helper.consume(source, core, kc, profiles.encode, previous, pure, rows)
    # Each source prefix (pure3 deficit, root5 deficit, cell5 deficit)
    # has twelve late-deficit/z vertices. Preserve those semantic blocks
    # so no certificate array descriptor exceeds the existing writer limit.
    conditional = statistics.pop('rows')
    require(len(conditional) == 1296, 'Complete conditional source rows')
    statistics['row_blocks'] = [conditional[start:start+12]
                                for start in range(0, len(conditional), 12)]
    statistics['row_blocks'] = [statistics['row_blocks'][start:start+6]
                                for start in range(0, 108, 6)]
    result = profiles.encode({'schema': 'erdos7-joint-survival-carriers-v1', **result,
                              'joint_survival': statistics, 'predecessor_source_profile_sha256': row_hash,
                              'source_sha256': pins | {'certificate_io.py': IO_PIN, PREVIOUS: PREVIOUS_PIN,
                                                        PREVIOUS_VERIFIER: PREVIOUS_VERIFIER_PIN},
                              'helper_sha256': {HELPER: HELPER_PIN},
                              'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest()})
    rendered = json.dumps(result, indent=2)+'\n'
    if args.output is not None:
        args.output.write_text(rendered)
    elif args.write:
        io.write_certificate_text(base/CERTIFICATE, rendered)
    else:
        actual = read(CERTIFICATE)
        require(json.dumps(actual, sort_keys=True, separators=(',', ':')) ==
                json.dumps(result, sort_keys=True, separators=(',', ':')), 'Full joint-carrier certificate reconstruction')
    print('PASS: canonical39 rows, three independent hinges,18 common carriers, conditional27/81 credit, all target endpoints, eight fallbacks and two complete cores.')
    print('Ordinary proof with exact rational arithmetic; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
