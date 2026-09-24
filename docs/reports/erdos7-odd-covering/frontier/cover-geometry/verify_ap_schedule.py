#!/usr/bin/env python3
"""Check all final AP(4,5) norms, continuous consumers and complete core tails."""
from pathlib import Path
from hashlib import sha256
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
IO_PIN = '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b'
SOURCE_PINS = {'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765', 'frontier/comparison-bounds/fixed_cost.py': '2df5ca217aced5823c6c9d88324737091b11318c9625f73503ca7cd35db8c21d', 'frontier/cover-geometry/layout_gap.py': 'f648a578745731d1b877655abaadd60ca8553f93d0ca5d41f32206b60ad7a23a', 'verify_killed_core_continuity.py': '6de7cb0f3aafa1d6db95017dd82c99d756e89b398996017ea1c1d77808f65226', 'certificates/layout_gap_frontier_certificate.json': 'bf7257ebfff334c8bf2bffa85959199d3c44e8e8fbf2a0a9cae2c6326ecf0c02', 'certificates/pure_root_profile_certificate.json': '045445deb47f22f4be3d06a8843a87b8ae4e8e19840aecd580c03e5ce3386d1a'}
LOCAL_PINS = {'frontier/cover-geometry/ap_schedule.py': '40b6138fc9d0fc1d540880e8a4abb1933d1dcd1b2c5dbf54646008c3f2e62b9f', 'frontier/cover-geometry/ap_schedule_core.py': '365b6c1f9a70dff5378a7d3a73a06879ee6193fbc69a4ac68ecfed1972e95617', 'certificates/ap_schedule_norms.json': '7cbb82bb2ea8691136fe74779632ffb821f78dd3b0c498ea1625f84a3866d9d8'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable module: ' + str(path))
    value = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(value)
    return value


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
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
    require(sha256((src / 'certificate_io.py').read_bytes()).hexdigest() == IO_PIN, 'Certificate IO source pin')
    io = module('ap_schedule_io', src / 'certificate_io.py')
    inputs = {name: io.read_artifact_bytes(src / name) for name in SOURCE_PINS}
    require(all(sha256(raw).hexdigest() == SOURCE_PINS[name] for name, raw in inputs.items()),
            'All complete mathematical predecessor source pins')
    require(all(sha256((base / name).read_bytes()).hexdigest() == pin for name, pin in LOCAL_PINS.items()),
            'Current AP schedule components and fixed-norm source pins')
    source = module('ap_schedule_source', src / 'verify_joint_frontier.py')
    source.source_pins(src)
    fixed = module('ap_schedule_fixed', src / 'frontier/comparison-bounds/fixed_cost.py')
    layout = module('ap_schedule_layout', src / 'frontier/cover-geometry/layout_gap.py')
    kc = module('ap_schedule_killed_core', src / 'verify_killed_core_continuity.py')
    for name, pin in kc.PINS.items():
        require(sha256(io.read_artifact_bytes(src / name)).hexdigest() == pin, 'Complete KC predecessor: ' + name)
    core = module('ap_schedule_core', base / 'frontier/cover-geometry/ap_schedule_core.py')
    math = module('ap_schedule_math', base / 'frontier/cover-geometry/ap_schedule.py')
    previous = json.loads(inputs['certificates/layout_gap_frontier_certificate.json'], object_pairs_hook=unique)
    pure = json.loads(inputs['certificates/pure_root_profile_certificate.json'], object_pairs_hook=unique)
    norms = json.loads((base / 'certificates/ap_schedule_norms.json').read_text(), object_pairs_hook=unique)

    def progress(done, total):
        if done % 216 == 0 or done == total:
            print('Checked AP(4,5) final norms at ' + str(done) + '/' + str(total), flush=True)

    result = math.reconstruct(source, fixed, layout, core, kc, previous, pure, norms, progress=progress)
    result['source_sha256'] = SOURCE_PINS | LOCAL_PINS | {'certificate_io.py': IO_PIN}
    result['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    certificate = base / 'certificates/ap_schedule_frontier_certificate.json'
    if args.write:
        io.write_certificate_text(certificate, json.dumps(result, indent=2) + '\n')
    else:
        require(json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=unique) == result,
                'Complete AP schedule target certificate matches final reconstruction')
    print('PASS: 596160 final norm margins; 1296 consumers, eight branches and complete core tails.')
    print('Joint upper bound ' + result['bound'] + ' = ' + str(float(math.F(result['bound']))))
    print('Ordinary proof and exact arithmetic; negative Q and unrestricted endpoint remain open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, ArithmeticError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
