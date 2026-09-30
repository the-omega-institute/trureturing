#!/usr/bin/env python3
"""Exact finite diagnostics for fixed primitive Fibonacci-response seeds.

Python 3.9+, standard library only; runnable from any working directory.
For each selected seed and prime, inspect indices 0 through twice the first
Fibonacci zero rank, then check the prescribed subinterval counts. These
finite checks do not establish an infinite zero-coset theorem, an average
prime tail, a density statement, Robin, RH, or a Lean theorem.
"""

import argparse
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path


def primes_through(limit):
    """Trial division with an exact integer square-root cutoff."""
    return [p for p in range(2, limit + 1)
            if all(p % d for d in range(2, isqrt(p) + 1))]


def first_rank(p):
    """Find the first zero using the original finite search budget."""
    u, v = 0, 1
    for z in range(1, 6 * p + 7):
        u, v = v, (u + v) % p
        if u == 0:
            return z
    raise AssertionError('no first rank within the selected search budget')


def check_seed(a, b, p, z):
    """Check V_j = a F_(j+3) + b F_(j+4) in the stated finite range."""
    assert (a or b) and gcd(a, b) == 1
    u, v = (2 * a + 3 * b) % p, (3 * a + 5 * b) % p
    values = []
    for _ in range(2 * z + 1):
        values.append(u)
        u, v = v, (u + v) % p
    zeros = [j for j, value in enumerate(values) if value == 0]
    residue = None
    if zeros:
        residue = zeros[0] % z
        assert zeros == [j for j in range(2 * z + 1) if j % z == residue]
    intervals = []
    for start in range(0, z + 1, max(1, z // 5)):
        end = min(2 * z, start + z // 2)
        count = sum(values[j] == 0 for j in range(start, end + 1))
        length = end - start + 1
        # Equivalent to count <= length / z + 1, without floating point.
        assert count * z <= length + z
        intervals.append([start, end, count])
    return {'seed': [a, b], 'prime': p, 'first_rank': z,
            'zero_residue': residue, 'zero_indices': zeros,
            'interval_start_end_zero_count': intervals}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', required=True, type=Path, help='output JSON file')
    args = parser.parse_args()
    if not __debug__:
        parser.error('assertions must be enabled; do not use -O or PYTHONOPTIMIZE')
    source = Path(__file__).resolve()
    if args.out.resolve() == source or (args.out.exists() and args.out.samefile(source)):
        parser.error('--out must not overwrite the program source')

    primes = primes_through(500)
    seeds = [(a, b) for a in range(9) for b in range(9)
             if (a or b) and gcd(a, b) == 1]
    checks = nonempty = interval_checks = 0
    rows_digest = hashlib.sha256()
    prime_rows = []
    for p in primes:
        z = first_rank(p)
        prime_nonempty = prime_intervals = 0
        for a, b in seeds:
            row = check_seed(a, b, p, z)
            rows_digest.update(json.dumps(row, sort_keys=True,
                                          separators=(',', ':')).encode('utf-8'))
            rows_digest.update(b'\n')
            checks += 1
            prime_nonempty += row['zero_residue'] is not None
            prime_intervals += len(row['interval_start_end_zero_count'])
        nonempty += prime_nonempty
        interval_checks += prime_intervals
        prime_rows.append({'prime': p, 'first_rank': z,
                           'checked_index_range': [0, 2 * z],
                           'nonempty_seed_zero_cosets': prime_nonempty,
                           'interval_count_checks': prime_intervals})

    report = {
        'schema': 'seed-zero-cosets-finite-v1',
        'source': source.name,
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope': 'Finite exact zero-coset and interval-count diagnostics only.',
        'response': 'V_j = a*F_(j+3) + b*F_(j+4), with F_0=0 and F_1=1',
        'ranges': {'seed_coordinate_bounds_inclusive': [0, 8],
                   'prime_bound_inclusive': 500,
                   'zero_check_indices': '0 <= j <= 2*z(p)',
                   'first_rank_search': '1 <= z <= 6*p+6',
                   'interval_starts': 'range(0, z+1, max(1, z//5))',
                   'interval_end': 'min(2*z, start+z//2)'},
        'seeds': [list(seed) for seed in seeds],
        'counts': {'seed_count': len(seeds), 'prime_count': len(primes),
                   'seed_prime_zero_coset_checks': checks,
                   'nonempty_zero_cosets': nonempty,
                   'interval_count_checks': interval_checks},
        'arithmetic': 'Integer arithmetic only; count*z <= interval_length+z.',
        'all_checked_rows_sha256': rows_digest.hexdigest(),
        'prime_rows': prime_rows,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n',
                        encoding='utf-8')
    print(json.dumps({'counts': report['counts'],
                      'source_sha256': report['source_sha256'],
                      'all_checked_rows_sha256': report['all_checked_rows_sha256']},
                     sort_keys=True))


if __name__ == '__main__':
    main()
