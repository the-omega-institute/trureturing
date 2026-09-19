#!/usr/bin/env python3
"""Check source deficits through the common actual AP survivor mass.

Python3.9+ standard library. Default and --check are read-only. Explicit
--write regenerates this certificate. Recorded dependency pins are checked;
the computation does not replay every mathematical ancestor.
"""
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2'
PREVIOUS = 'certificates/source_norms/retained-transport/retained_quadratic_tests.json'
PREVIOUS_PIN = '6a58a6155bb2f860fda843848d54397f0e4ece26cab40f8f1676a857631e8fec'
PREVIOUS_VERIFIER = 'frontier/retained-transport/verify_retained_quadratic_tests.py'
PREVIOUS_VERIFIER_PIN = '063509eb7bf8279e90a95d23184ecf474396ead47866961cc4c3568778db342f'
LOCAL_PINS = {
    'frontier/source-budgets/shared_source_deficits.py': 'e836b66691213273f272db6bd992f202897fda6bcf336551ab50f41c9a55e883',
    'frontier/source-budgets/shared_source_consumer.py': '02642a68c8e1c351988f654081757e3b6594cfa4411eabea267593d3658aebf5',
    'frontier/source-budgets/shared_linear_refinement.py': '2150065bb9eb9369847cf399e9f14b78406b4aecfaa2da10ea2d00eff8d0fe7e',
    'frontier/source-budgets/shared_square_barrier.py': '6bc57d9b93bc583bbced72092f722a4369743013e0dd9eeea0703f01a3bf10a1',
}
CERTIFICATE = 'certificates/source_norms/source-budgets/shared_source_deficits.json'


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
    parser.add_argument('--source-directory', type=Path, default=base)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = args.source_directory.resolve()
    require(sha256((src/'certificate_io.py').read_bytes()).hexdigest() == IO_PIN, 'Certificate IO source pin')
    io = module('shared_source_io', src/'certificate_io.py')
    raw = io.read_artifact_bytes(src/PREVIOUS)
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Complete logical quadratic predecessor pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((src/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Predecessor verifier pin')
    pins = previous['source_sha256'] | previous['helper_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(src/name)).hexdigest() == pin, 'Predecessor direct source pin: '+name)
    for name, pin in LOCAL_PINS.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Current mathematics source pin: '+name)

    def read(name):
        return json.loads(io.read_artifact_bytes(src/name), object_pairs_hook=unique)

    source = module('shared_source_math', src/'verify_joint_frontier.py')
    fixed = module('shared_source_fixed', src/'frontier/comparison-bounds/fixed_cost.py')
    layout = module('shared_source_layout', src/'frontier/cover-geometry/layout_gap.py')
    ap = module('shared_source_ap', src/'frontier/cover-geometry/ap_schedule.py')
    core = module('shared_source_core', src/'frontier/cover-geometry/ap_schedule_core.py')
    kc = module('shared_source_kc', src/'verify_killed_core_continuity.py')
    old = module('shared_source_old', src/'frontier/retained-transport/retained_five_tests.py')
    helper = module('shared_source_profiles', base/'frontier/source-budgets/shared_source_deficits.py')
    consumer = module('shared_source_consumer', base/'frontier/source-budgets/shared_source_consumer.py')
    refine = module('shared_source_linear_refinement', base/'frontier/source-budgets/shared_linear_refinement.py')
    square = module('shared_source_square_barrier', base/'frontier/source-budgets/shared_square_barrier.py')
    parent = read('certificates/ap_schedule_frontier_certificate.json')
    pure = read('certificates/pure_root_profile_certificate.json')
    ap_inputs = read('certificates/ap_schedule_norms.json')
    quadratic_inputs = read('certificates/source_norms/retained-transport/retained_quadratic_inputs.json')

    def progress(done, total):
        if done % 216 == 0 or done == total:
            print('Checked shared-source deficits at '+str(done)+'/'+str(total), flush=True)

    rows, statistics = helper.aggregate(source, fixed, layout, ap, parent, previous,
                                         quadratic_inputs, ap_inputs, progress)
    preceding_source = read('certificates/source_norms/retained-transport/retained_five_tests.json')
    require(statistics['source_margin_sha256'] == preceding_source['source_norm']['margin_sha256'],
            'Every source margin matches its published predecessor')
    rows, refinement = refine.refine(source, fixed, ap, ap_inputs, rows)
    rows, square_refinement = square.refine(source, fixed, rows, statistics['quadratic_tail_weight'])
    result = consumer.consumer(source, core, kc, old, parent, previous, pure, rows,
                               square_refinement['source_barrier'], refinement['H41_increase'])
    result = helper.encode({'schema': 'erdos7-shared-source-deficits-v1', **result,
                            'source_profiles': statistics, 'linear_refinement': refinement,
                            'square_barrier_refinement': square_refinement,
                            'source_profile_sha256': sha256(json.dumps(helper.encode(rows), sort_keys=True,
                                             separators=(',', ':')).encode()).hexdigest(),
                            'source_sha256': pins | {'certificate_io.py': IO_PIN, PREVIOUS: PREVIOUS_PIN,
                                                      PREVIOUS_VERIFIER: PREVIOUS_VERIFIER_PIN},
                            'helper_sha256': LOCAL_PINS,
                            'verifier_sha256': sha256(Path(__file__).read_bytes()).hexdigest(),
                            'scope': 'Ordinary same-law raw-mass inequalities and exact rational arithmetic. All finite original heights and independent labels retained. Negative Q, arbitrary later-prime continuation and unrestricted Erdos7 remain open.'})
    certificate = base/CERTIFICATE
    if args.write:
        io.write_certificate_text(certificate, json.dumps(result, indent=2)+'\n')
    else:
        actual = json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=unique)
        require(json.dumps(actual, sort_keys=True, separators=(',', ':')) ==
                json.dumps(result, sort_keys=True, separators=(',', ':')), 'Complete shared-source certificate reconstruction')
    print('PASS: complete source deficits, same-mass consumer, eight fallbacks and both core errors.')
    print('Ordinary rational verification; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
