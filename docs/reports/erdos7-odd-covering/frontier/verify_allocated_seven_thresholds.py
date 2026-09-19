#!/usr/bin/env python3
"""Check fixed full-root threshold allocations with complete geometric tails.

Reconstruct all source39 rows and all old46 full/partial margins. Reuse
pinned47/49 numerator values, then check all signed endpoints and cores.
Default/--check is read-only; --output writes standalone exact JSON;
--write uses the existing canonical certificate writer. No Lean claim.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232'
PREVIOUS = 'certificates/source_norms/full_linear_carrier_frontier.json'
PREVIOUS_PIN = '237ed11241550037c69c855742d3f6e0a3a9c362ae2a861a173d3450e32375c0'
PREVIOUS_VERIFIER = 'frontier/verify_full_linear_carrier_frontier.py'
PREVIOUS_VERIFIER_PIN = '1a97de206716b5ae1822ffca4b94e5affb3be78e763002bdf554d3a95ac8f948'
HELPER = 'frontier/allocated_seven_thresholds.py'
HELPER_PIN = 'b467824a30899cd14ab35ab4a1383c4a3848e5c9dcbdaebd6f4074e9a1d8e78d'
CERTIFICATE = 'certificates/source_norms/allocated_seven_thresholds.json'


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
    io = module('allocated_io', base/'certificate_io.py')
    raw = io.read_artifact_bytes(base/PREVIOUS)
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Logical profile49 certificate pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['schema'] == 'erdos7-full-linear-carrier-frontier-v1'
            and previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((base/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Published49 verifier identity')
    pins = previous['source_sha256'] | previous['helper_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(base/name)).hexdigest() == pin,
                'Inherited source or logical certificate pin: '+name)
    require(sha256((base/HELPER).read_bytes()).hexdigest() == HELPER_PIN, 'Current helper pin')

    def read(name):
        return json.loads(io.read_artifact_bytes(base/name), object_pairs_hook=unique)

    def load(name, path):
        return module('allocated_'+name, base/path)

    source = load('source', 'verify_joint_frontier.py')
    fixed = load('fixed', 'frontier/fixed_cost.py')
    layout = load('layout', 'frontier/layout_gap.py')
    ap = load('ap', 'frontier/ap_schedule.py')
    core = load('core', 'frontier/ap_schedule_core.py')
    kc = load('kc', 'verify_killed_core_continuity.py')
    profiles = load('profiles', 'frontier/shared_source_deficits.py')
    linear = load('linear', 'frontier/shared_linear_refinement.py')
    square = load('square', 'frontier/shared_square_barrier.py')
    helper = load('helper', HELPER)
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    quadratic = read('certificates/source_norms/retained_quadratic_tests.json')
    pure = read('certificates/pure_root_profile_certificate.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    quadratic_inputs = read('certificates/source_norms/retained_quadratic_inputs.json')
    previous39 = read('certificates/source_norms/shared_source_deficits.json')
    previous46 = read('certificates/source_norms/joint_survival_carriers.json')
    previous47 = read('certificates/source_norms/joint_linear_carriers.json')

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
            and profiles.encode(linear_stats) == previous39['linear_refinement']
            and profiles.encode(square_stats) == previous39['square_barrier_refinement'],
            'Complete published39 source and refinement statistics')
    row_hash = sha256(json.dumps(profiles.encode(rows), sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    require(row_hash == previous39['source_profile_sha256'] == previous['predecessor_source_profile_sha256'],
            'Complete reconstructed39 source digest')
    rows, statistics = helper.reconstruct(source, previous46, rows, progress('Allocated full/partial margins'))
    result = helper.consume(source, core, kc, previous47, previous, pure, rows)
    result = profiles.encode({'schema': 'erdos7-allocated-seven-thresholds-v1', **result,
                              'allocation_statistics': statistics,
                              'predecessor_source_profile_sha256': row_hash,
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
                json.dumps(result, sort_keys=True, separators=(',', ':')), 'Exact allocated-threshold certificate')
    print('PASS: complete39 reconstruction,46656 old46 full/partial margins, pinned47/49 numerators,233280 signed endpoint inequalities,8 fallbacks,2 complete cores.')
    print('Ordinary proof and exact rational arithmetic; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
