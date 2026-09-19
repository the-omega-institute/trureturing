#!/usr/bin/env python3
"""Check five retained-event AP45 quadratic norms and their complete consumer.

Python3.9+ standard library. Default and --check only read files; explicit
--write regenerates the result certificate. Source pins bind the complete
predecessor and its direct sources, without replaying every ancestor proof.
"""
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '3bab29ebc23defcae75e775fb182d2aa0d83d71ba1ae3b168ed8e9bc7a8c1fe2'
PREVIOUS = 'certificates/source_norms/retained-transport/retained_five_tests.json'
PREVIOUS_PIN = '3f30d24b9d66c6c24a3ee8361b0fb2c5fe6e86ebe4f4b9332fd0b5602954a30e'
PREVIOUS_VERIFIER = 'frontier/retained-transport/verify_retained_five_tests.py'
PREVIOUS_VERIFIER_PIN = '538de506f0d4b9628654b2a64f3771259ae7a56bead7ac4e88a743ba4a81c90a'
HELPER = 'frontier/retained-transport/retained_quadratic_tests.py'
HELPER_PIN = '712cf9a4adab36feff0a2ed8b64e6b721e22bcbfa2eb26fede154f049d06f670'
INPUTS = 'certificates/source_norms/retained-transport/retained_quadratic_inputs.json'
INPUTS_PIN = 'f5353ddbbf7d95ddbc160395272a79611011ac3605d82ad53cabda2127ebb710'
CERTIFICATE = 'certificates/source_norms/retained-transport/retained_quadratic_tests.json'


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
    require(spec is not None and spec.loader is not None, 'Loadable module: '+str(path))
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
    io = module('retained_quadratic_io', src/'certificate_io.py')
    raw = io.read_artifact_bytes(src/PREVIOUS)
    require(sha256(raw).hexdigest() == PREVIOUS_PIN, 'Complete source-improvement predecessor pin')
    previous = json.loads(raw, object_pairs_hook=unique)
    require(previous['verifier_sha256'] == PREVIOUS_VERIFIER_PIN
            and sha256((src/PREVIOUS_VERIFIER).read_bytes()).hexdigest() == PREVIOUS_VERIFIER_PIN,
            'Published source-improvement verifier pin')
    pins = previous['source_sha256'] | previous['helper_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(src/name)).hexdigest() == pin,
                'Complete predecessor direct mathematical source pin: '+name)
    local = {HELPER: HELPER_PIN, INPUTS: INPUTS_PIN}
    for name, pin in local.items():
        require(sha256((base/name).read_bytes()).hexdigest() == pin, 'Current calculation pin: '+name)
    inputs = json.loads((base/INPUTS).read_text(), object_pairs_hook=unique)
    helper = module('retained_quadratic_math', base/HELPER)
    source = module('retained_quadratic_source', src/'verify_joint_frontier.py')
    fixed = module('retained_quadratic_fixed', src/'frontier/comparison-bounds/fixed_cost.py')
    layout = module('retained_quadratic_layout', src/'frontier/cover-geometry/layout_gap.py')
    ap = module('retained_quadratic_ap', src/'frontier/cover-geometry/ap_schedule.py')
    core = module('retained_quadratic_core', src/'frontier/cover-geometry/ap_schedule_core.py')
    kc = module('retained_quadratic_kc', src/'verify_killed_core_continuity.py')
    previous_math = module('retained_quadratic_previous', src/'frontier/retained-transport/retained_five_tests.py')
    parent = json.loads(io.read_artifact_bytes(src/'certificates/ap_schedule_frontier_certificate.json'),
                        object_pairs_hook=unique)
    pure = json.loads(io.read_artifact_bytes(src/'certificates/pure_root_profile_certificate.json'),
                      object_pairs_hook=unique)

    def progress(done, total):
        if done % 216 == 0 or done == total:
            print('Checked retained quadratic norms at '+str(done)+'/'+str(total), flush=True)

    result = helper.reconstruct(source, fixed, layout, ap, core, kc, previous_math,
                                parent, previous, pure, inputs, progress)
    result['source_sha256'] = pins | {'certificate_io.py': IO_PIN, PREVIOUS: PREVIOUS_PIN,
                                      PREVIOUS_VERIFIER: PREVIOUS_VERIFIER_PIN}
    result['helper_sha256'] = local
    result['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    certificate = base/CERTIFICATE
    if args.write:
        certificate.parent.mkdir(parents=True, exist_ok=True)
        io.write_certificate_text(certificate, json.dumps(result, indent=2)+'\n')
    else:
        actual = json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=unique)
        require(json.dumps(actual, sort_keys=True, separators=(',', ':')) ==
                json.dumps(result, sort_keys=True, separators=(',', ':')),
                'Complete retained quadratic certificate matches exact reconstruction')
    print('PASS: 648000 final norm margins; 1296 AP45 vertices, eight fallbacks and two complete core tails.')
    print('Joint upper bound '+result['bound']+' = '+str(float(helper.F(result['bound']))))
    print('Ordinary proof and exact rational arithmetic; negative Q and unrestricted Erdos7 remain open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
