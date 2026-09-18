#!/usr/bin/env python3
"""Verify fixed layout-distance norms and the unchanged AP(4,6) consumer."""
from pathlib import Path
from hashlib import sha256
import argparse
import importlib.util
import json
import sys

sys.dont_write_bytecode = True

# Filled from complete logical predecessor inputs, including split certificates.
IO_PIN = '287582353eeb0674f4e80530ebf268228b023f6088d14c819488a56111d0b232'
SOURCE_PINS = {'verify_joint_frontier.py': 'a40fce0a5cb6a713dc8cb569b874d284b8dd66fb3f0a5e48fc2c69cb8fe286fe', 'certificates/joint_frontier_certificate.json': 'be01369024cf8a3a43efdfa5e18334d8ba3d07c96f25801c9a919a364c55a583', 'certificates/fixed_cost_frontier_certificate.json': '4c6042eaaef211e4991e350ddc128f910316c467bc3dd1630b3c0468f270a133'}
LOCAL_PINS = {'frontier/layout_gap.py': 'f648a578745731d1b877655abaadd60ca8553f93d0ca5d41f32206b60ad7a23a', 'certificates/layout_gap_norms.json': 'a5ca5849e50702035e6812311d2191beb13498e2dc81b7dbb13eab27ffc2ebf5'}


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
    base = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-directory', type=Path, default=base)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    src = args.source_directory.resolve()
    io_path = src / 'certificate_io.py'
    require(sha256(io_path.read_bytes()).hexdigest() == IO_PIN, 'Certificate IO source pin')
    io = module('layout_gap_io', io_path)
    inputs = {name: io.read_artifact_bytes(src / name) for name in SOURCE_PINS}
    require(all(sha256(raw).hexdigest() == SOURCE_PINS[name] for name, raw in inputs.items()),
            'All complete mathematical predecessor source pins')
    require(all(sha256((base / name).read_bytes()).hexdigest() == pin for name, pin in LOCAL_PINS.items()),
            'Current layout-gap component and fixed-norm source pins')
    source = module('layout_gap_source', src / 'verify_joint_frontier.py')
    source.source_pins(src)
    math = module('layout_gap_math', base / 'frontier/layout_gap.py')
    consumer = json.loads(inputs['certificates/joint_frontier_certificate.json'], object_pairs_hook=unique)
    previous = json.loads(inputs['certificates/fixed_cost_frontier_certificate.json'], object_pairs_hook=unique)
    norms = json.loads((base / 'certificates/layout_gap_norms.json').read_text(), object_pairs_hook=unique)

    def progress(done, total):
        if done % 216 == 0 or done == total:
            print('Checked layout-gap final norms at ' + str(done) + '/' + str(total), flush=True)

    result = math.reconstruct(source, consumer, previous, norms, progress=progress)
    result['source_sha256'] = SOURCE_PINS | LOCAL_PINS | {'certificate_io.py': IO_PIN}
    result['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    certificate = base / 'certificates/layout_gap_frontier_certificate.json'
    if args.write:
        io.write_certificate_text(certificate, json.dumps(result, indent=2) + '\n')
    else:
        require(json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=unique) == result,
                'Complete layout-gap target certificate matches final reconstruction')
    print('PASS: 12960 source-square + 64800 quadratic margins; 1296 consumer vertices and 8 branches.')
    print('Joint upper bound ' + result['bound'] + ' = ' + str(float(math.F(result['bound']))))
    print('Ordinary proof with exact arithmetic; unrestricted endpoint and later-prime continuation remain open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
