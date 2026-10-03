#!/usr/bin/env python3
"""Check a fixed full shallow family and its arbitrary-core-height certificate.

The native checker sieves every numerical residue and folds all divisors.
Only the standard library and clang++ are required. This is finite exact
arithmetic, not Lean verification or a theorem for arbitrary shallow phases.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import prod
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse
import json
import subprocess


DEPENDENCIES = {'fibre_credit_depth_two_fullmulti_actual_certificate.json': '10a8754712272fb4e16fe548dc909a9ee65289bdfbef88180d03080ebb519248', 'fibre_credit_depth_two_fullmulti_actual_sieve.cpp': '219906813033b8b22cce46bf80a6082d6a04a6aabde8de69a11c9d092b1c0759', 'fibre_credit_depth_two_fullmulti_joint_input.json': '9d1e21705c4e618c70db324b143cf732371ceaf79e3470d4c66b8260bb6ae4e9'}
PRIMES = (11, 13, 17, 19, 23)
DIVISORS = (1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105, 315)


def check(value, message):
    if not value:
        raise ValueError(message)


def coefficient(d):
    return prod(F(p, p - 1) for p, h in ((3, 9), (5, 5), (7, 7)) if d % h == 0) - 1


def calculate():
    directory = Path(__file__).resolve().parent
    check(len(DEPENDENCIES) == 3, 'complete numerical certificate input interface')
    for name, digest in DEPENDENCIES.items():
        check(sha256((directory / name).read_bytes()).hexdigest() == digest,
              'pinned fullmulti dependency: ' + name)
    literal = json.loads((directory / 'fibre_credit_depth_two_fullmulti_actual_certificate.json').read_text())
    carrier = 315 * prod(PRIMES)
    moduli = {d * prod(p for i, p in enumerate(PRIMES) if j >> i & 1)
              for d in DIVISORS for j in range(32)} - {1}
    rules = json.loads((directory / 'fibre_credit_depth_two_fullmulti_joint_input.json').read_text())['originals']
    check(literal['carrier'] == carrier == 334639305, 'declared actual carrier')
    check(len(rules) == len({m for m, a in rules}) == len(moduli) == 383,
          '383 distinct numerical slots')
    check({m for m, a in rules} == moduli, 'every nonunit shallow divisor is present')
    check(all(type(a) is int and 0 <= a < m for m, a in rules), 'fixed legal phases')
    core = [(m, a) for m, a in rules if 315 % m == 0]
    expected_core = [(3, 0), (5, 0), (7, 0), (9, 4), (15, 11), (21, 8),
                     (35, 9), (45, 1), (63, 1), (105, 59), (315, 179)]
    check(sorted(core) == expected_core, 'literal actual core family')
    rows = [x for x in range(315) if all(x % m != a for m, a in core)]
    check(len(rows) == 75, 'actual core survivor count')
    used = [sorted({a % p for m, a in rules if m % p == 0} - {0}) for p in PRIMES]
    check(all(roots == list(range(1, p)) for p, roots in zip(PRIMES, used)),
          'every live root occurs in an actual original')
    expected_queries = {(d, j): d * prod(p for i, p in enumerate(PRIMES) if j >> i & 1)
                        for d in DIVISORS if coefficient(d) > 0 for j in range(32)}
    caps = literal['query_caps']
    observed = {(r['core_divisor'], r['outside_mask']): r['modulus'] for r in caps}
    check(len(caps) == len(observed) == 320 and observed == expected_queries,
          'complete nonzero joint-query inventory')
    check(all(type(r['cap']) is int and 0 < r['cap'] <= carrier for r in caps),
          'integral query cap candidates')
    source = directory / 'fibre_credit_depth_two_fullmulti_actual_sieve.cpp'
    with TemporaryDirectory(prefix='e7_fullmulti_', dir='/tmp') as name:
        temporary = Path(name)
        binary, input_file, output = temporary / 'sieve', temporary / 'input.txt', temporary / 'result.json'
        lines = [f"{carrier} {literal['survivor_count']} 383"]
        lines += [f'{m} {a}' for m, a in rules]
        lines += ['320'] + [f"{r['modulus']} {r['cap']}" for r in caps]
        input_file.write_text('\n'.join(lines) + '\n')
        subprocess.run(['clang++', '-std=c++17', '-O3', '-fsanitize=undefined',
                        '-fno-sanitize-recover=undefined', str(source), '-o', str(binary)],
                       check=True, capture_output=True)
        subprocess.run([str(binary), str(input_file), str(output)], check=True, capture_output=True)
        verified = json.loads(output.read_text())
    check(verified['passed'] and verified['numerical_divisors'] == 384 and
          verified['exact_query_maxima'] == 320, 'complete numerical reconstruction')
    mass = verified['survivor_count']
    check(mass == literal['survivor_count'] == 27939653, 'full actual survivor set')
    by_size = [F(0) for _ in range(6)]
    for row in caps:
        by_size[row['outside_mask'].bit_count()] += coefficient(row['core_divisor']) * row['cap']
    debit = sum(by_size)
    margin = mass - debit
    check(48 * debit == 1220322441 and margin == F(40260301, 16), 'exact actual higher-core reserve')
    lower = margin / carrier
    check(lower == F(2368253, 314954640) > F(1, 133), 'uniform core-height Haar lower bound')
    return {'scope': 'One literal full383-slot shallow phase family on3/5/7/11/13/17/19/23; all later core3/5/7 heights and phases arbitrary, outside exponents at most1.',
            'carrier': carrier, 'original_count': len(rules), 'core_originals': expected_core,
            'core_survivor_count': len(rows), 'outside_used_live_roots': [len(a) for a in used],
            'survivor_count': mass, 'exact_joint_query_count': len(caps),
            'debit48_by_support_size': [int(48 * v) for v in by_size],
            'higher_core_debit': str(debit), 'higher_core_margin': str(margin),
            'normalized_debit': str(debit / mass), 'Haar_survivor_lower': str(lower),
            'strict_simple_lower': '1/133', 'numerical_reconstruction': verified,
            'dependency_hashes': DEPENDENCIES, 'lean_verification': False,
            'uniform_over_shallow_phases': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = json.loads(json.dumps(calculate()))
    rendered = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output is None:
        check(json.loads(Path(__file__).resolve().with_suffix('.json').read_text()) == result,
              'retained result agrees with fullmulti numerical certificate')
        print(rendered, end='')
    else:
        args.output.write_text(rendered)


if __name__ == '__main__':
    main()
