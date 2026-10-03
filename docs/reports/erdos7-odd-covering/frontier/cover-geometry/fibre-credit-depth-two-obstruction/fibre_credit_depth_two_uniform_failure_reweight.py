#!/usr/bin/env python3
"""One actual family defeats the uniform certificate and admits fixed row weights.

The negative certificate directly sieves the full numerical carrier and
counts60 fixed query cylinders. The positive certificate reuses Report756's
literal-only intersection calculation with one fixed75-row weight vector.
Neither uses a solver or assumes an optimized source or query phase.
"""
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import importlib.util
import json
import subprocess


DEPENDENCIES = {'fibre_credit_depth_two_fullmulti_joint_saving.py': '251fbe7c2833404c10003c8a0936334c8ca3968b85c2b2543d10b97f9ce32021', 'fibre_credit_depth_two_uniform_failure_reweight_input.json': '0676a756b6e846fb3b63ff8a4d4838ff83bcc0fc095296c465dadbfde1ec9ed3', 'fibre_credit_depth_two_uniform_failure_sieve.cpp': '7d3717d7fa81509980cbb20776be16df578112b011373a0074927a37670ccd43'}


def check(value, message):
    if not value:
        raise ValueError(message)


def calculate():
    directory = Path(__file__).resolve().parent
    check(len(DEPENDENCIES) == 3, 'complete uniform/reweight input interface')
    for name, digest in DEPENDENCIES.items():
        check(sha256((directory / name).read_bytes()).hexdigest() == digest,
              'pinned uniform-reweight dependency: ' + name)
    raw = json.loads((directory / 'fibre_credit_depth_two_uniform_failure_reweight_input.json').read_text())
    shared = directory / 'fibre_credit_depth_two_fullmulti_joint_saving.py'
    spec = importlib.util.spec_from_file_location('e7_fixed_joint_certificate', shared)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    # Validates every numerical slot, phase, row weight and forest edge,
    # and computes all intersections and source caps with these SAME weights.
    positive = module.evaluate(raw)
    check(positive['maximum_weight'] == 105 and len(raw['row_weights']) == 75,
          'literal small integer weight vector')
    check(sum(w > 0 for x, w in raw['row_weights']) == 60, 'positive actual core rows')
    check(positive['compact_margin_lower48'] == 5746587945,
          'same-source positive reweighted reserve')
    check(F(positive['Haar_survivor_lower']) == F(459911, 134980560) > F(1, 294),
          'arbitrary finite core-height lower bound')
    source = directory / 'fibre_credit_depth_two_uniform_failure_sieve.cpp'
    with TemporaryDirectory(prefix='e7_uniform_reweight_', dir='/tmp') as name:
        temporary = Path(name)
        binary, phases, output = temporary / 'sieve', temporary / 'phases.txt', temporary / 'negative.json'
        phases.write_text('383\n' + ''.join(f'{m} {a}\n' for m, a in raw['originals']))
        subprocess.run(['clang++', '-std=c++17', '-O3', '-fsanitize=undefined',
                        '-fno-sanitize-recover=undefined', str(source), '-o', str(binary)],
                       check=True, capture_output=True)
        subprocess.run([str(binary), str(phases), str(output)], check=True, capture_output=True)
        negative = json.loads(output.read_text())
    check(negative['passed'] and negative['uniform_J_upper48'] == -72775703,
          'strict actual uniform-source obstruction')
    check(negative['carrier'] == positive['carrier'] == raw['carrier'],
          'one common actual family and carrier')
    used = [sorted({a % p for m, a in raw['originals'] if m % p == 0} - {0})
            for p in raw['outside_primes']]
    check(all(roots == list(range(1, p)) for roots, p in zip(used, raw['outside_primes'])),
          'all live outside roots appear in actual originals')
    return {'scope': __doc__, 'uniform_negative_certificate': negative,
            'reweighted_positive_certificate': positive,
            'outside_used_live_roots': [len(a) for a in used],
            'uniform_source_is_entire_actual_survivor_set': True,
            'same_literal_originals_in_both_certificates': True,
            'all_reweightings_excluded': False, 'uniform_over_shallow_phases': False,
            'dependency_hashes': DEPENDENCIES, 'lean_verification': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = calculate()
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        check(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
              'retained result agrees with uniform failure and same-family reweighting')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
