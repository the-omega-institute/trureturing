#!/usr/bin/env python3
"""Check fixed convex source norms on every original parameter vertex.

All source probabilities and complete tails are those of the accompanying
ordinary proof. This verifies exact finite envelopes, not a Lean endpoint.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import importlib.util
import json
import sys

IO_PIN = '2318639f574d9f6fab4c7187c2736cde559e1925a5f9fa657afe0b8334f7d02b'
SOURCE_PINS = {
    'verify_joint_frontier.py': '0b5cd35851d36f3af83aee19e02267cb05abc8bf07611a12083fca6f3d9bd765',
    'certificates/joint_frontier_certificate.json': 'abee2fd2a2038029cf74c59615501463a4b289d5e071d2c17de2ede6288d6ce8',
    'frontier/comparison-bounds/fixed_cost.py': '2df5ca217aced5823c6c9d88324737091b11318c9625f73503ca7cd35db8c21d',
    'certificates/fixed_cost_norms.json': 'dc4f440a5718bbf9c2ded831b6cb10c687e18df972270ab7b5f521430b225797',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, 'Loadable source: ' + str(path))
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
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--write', action='store_true')
    modes.add_argument('--check', action='store_true')
    args = parser.parse_args()
    io_path = base / 'certificate_io.py'
    require(sha256(io_path.read_bytes()).hexdigest() == IO_PIN, 'Certificate IO source pin')
    io = module('fixed_cost_io', io_path)
    inputs = {name: io.read_artifact_bytes(base / name) for name in SOURCE_PINS}
    require(all(sha256(raw).hexdigest() == SOURCE_PINS[name] for name, raw in inputs.items()),
            'Every mathematical input has its pinned complete identity')
    source = module('fixed_cost_source', base / 'verify_joint_frontier.py')
    source.source_pins(base)
    math = module('fixed_cost_math', base / 'frontier/comparison-bounds/fixed_cost.py')
    consumer = json.loads(inputs['certificates/joint_frontier_certificate.json'], object_pairs_hook=unique)
    norms = json.loads(inputs['certificates/fixed_cost_norms.json'], object_pairs_hook=unique)

    def progress(done, total):
        if done % 216 == 0 or done == total:
            print('Checked fixed norms at ' + str(done) + '/' + str(total) + ' vertices', flush=True)

    result = math.reconstruct(source, consumer, norms, progress=progress)
    result['source_sha256'] = SOURCE_PINS | {'certificate_io.py': IO_PIN}
    result['verifier_sha256'] = sha256(Path(__file__).read_bytes()).hexdigest()
    certificate = base / 'certificates/fixed_cost_frontier_certificate.json'
    if args.write:
        io.write_certificate_text(certificate, json.dumps(result, indent=2) + '\n')
    else:
        require(json.loads(io.read_artifact_bytes(certificate), object_pairs_hook=unique) == result,
                'Complete fixed-cost certificate matches reconstruction')
    print('PASS: ' + str(result['direct_norm_margin_checks']) + ' final norm margins; full AP tails.')
    print('Joint upper bound ' + result['bound'] + ' = ' + str(float(math.F(result['bound']))))
    print('Ordinary proof with exact arithmetic; unrestricted endpoint and prime continuation remain open.')


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, json.JSONDecodeError) as error:
        print('FAIL: ' + str(error), file=sys.stderr)
        sys.exit(1)
