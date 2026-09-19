#!/usr/bin/env python3
"""Check the retained original 5,15,45 source bound and complete AP45 consumer.

Python3.9+ standard library. Default and --check only read files. --write
explicitly regenerates this checker's certificate. Source bindings cover
the published parent, its verifier and its recorded direct dependencies;
they do not replay every ancestor proof or its original AP norm checks.
"""
from hashlib import sha256
from pathlib import Path
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232'
PARENT = 'certificates/ap_schedule_frontier_certificate.json'
PARENT_PIN = '85bc95f89121f2492cedf3d8db228434c49f04650645b789780b359c54ac4b40'
PARENT_VERIFIER = 'frontier/verify_ap_schedule.py'
PARENT_VERIFIER_PIN = '73c01b9da8b511312e699545cd633cb17d7533431d1ce368d43e1156ed585e70'
HELPER = 'frontier/retained_five_tests.py'
HELPER_PIN = '3dc81efd29363a9eedb43ffeb9dc38cdb294ddc547050428885393a05f1d9c60'
CERTIFICATE = 'certificates/source_norms/retained_five_tests.json'


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
    base = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-directory', type=Path, default=base)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = args.source_directory.resolve()
    require(sha256((src/'certificate_io.py').read_bytes()).hexdigest() == IO_PIN,
            'Certificate IO source pin')
    io = module('retained_five_io', src/'certificate_io.py')
    raw = io.read_artifact_bytes(src/PARENT)
    require(sha256(raw).hexdigest() == PARENT_PIN, 'Complete logical AP45 parent pin')
    parent = json.loads(raw, object_pairs_hook=unique)
    require(parent['verifier_sha256'] == PARENT_VERIFIER_PIN and
            sha256((src/PARENT_VERIFIER).read_bytes()).hexdigest() == PARENT_VERIFIER_PIN,
            'Published AP45 verifier source pin')
    pins = parent['source_sha256']
    for name, pin in pins.items():
        require(sha256(io.read_artifact_bytes(src/name)).hexdigest() == pin,
                'Published parent direct mathematical source pin: '+name)
    require(sha256((base/HELPER).read_bytes()).hexdigest() == HELPER_PIN,
            'Current retained-five mathematics helper pin')
    helper = module('retained_five_math', base/HELPER)
    source = module('retained_five_source', src/'verify_joint_frontier.py')
    core = module('retained_five_core', src/'frontier/ap_schedule_core.py')
    kc = module('retained_five_kc', src/'verify_killed_core_continuity.py')
    previous = json.loads(io.read_artifact_bytes(
        src/'certificates/layout_gap_frontier_certificate.json'), object_pairs_hook=unique)
    pure = json.loads(io.read_artifact_bytes(
        src/'certificates/pure_root_profile_certificate.json'), object_pairs_hook=unique)
    result = helper.reconstruct(source, core, kc, parent, previous, pure)
    result['source_sha256'] = pins | {'certificate_io.py': IO_PIN, PARENT: PARENT_PIN,
                                      PARENT_VERIFIER: PARENT_VERIFIER_PIN}
    result['helper_sha256'] = {HELPER: HELPER_PIN}
    result['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    certificate = base/CERTIFICATE
    if args.write:
        certificate.parent.mkdir(parents=True, exist_ok=True)
        io.write_certificate_text(certificate, json.dumps(result, indent=2)+'\n')
    else:
        actual = json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=unique)
        require(json.dumps(actual, sort_keys=True, separators=(',', ':')) ==
                json.dumps(result, sort_keys=True, separators=(',', ':')),
                'Complete retained-five certificate matches exact reconstruction')
    print('PASS: 129600 source margins, 12960 predecessor source checks, 1296 AP45 vertices, eight fallbacks and two complete core tails.')
    print('Ordinary proof and exact rational arithmetic; unrestricted Erdos7 remains open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: '+str(error), file=sys.stderr)
        sys.exit(1)
