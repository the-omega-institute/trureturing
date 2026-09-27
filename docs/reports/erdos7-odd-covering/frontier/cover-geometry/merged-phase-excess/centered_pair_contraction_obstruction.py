#!/usr/bin/env python3
"""Exclude every specified centered two-parent contraction of the463 family.

Only explicit --originals, --blockers and --output paths are accessed.
Enumerate original same-prime power children, retaining actual labels,
heights and phases. A literal old private point certifies every failure.
No random search, solver or stored candidate list is used. Checks survive -O.
"""

import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from math import gcd, isqrt, lcm
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def evaluate(originals, extra):
    rows = originals['originals']
    require(len(rows) == 463, 'expected the463 original classes')
    require(all(type(row[key]) is int for row in rows
                for key in ('modulus', 'residue', 'private_point')), 'noninteger input')
    A = {row['modulus']: row['residue'] for row in rows}
    primary = {row['modulus']: row['private_point'] for row in rows}
    require(len(A) == len(rows), 'duplicate original modulus')
    require(all(m > 1 and m % 2 == 1 and 0 <= a < m for m, a in A.items()),
            'invalid original odd AP')
    period = lcm(*A)
    require(period == 481225870125, 'unexpected original period')
    primes = [m for m in sorted(A) if is_prime(m)]
    require(primes == [3, 5, 7, 11, 13, 17, 19], 'unexpected original primes')
    require(all(A[p] == 0 for p in primes), 'prime normalization fails')
    for m in A:
        for d in range(2, isqrt(m) + 1):
            if m % d == 0:
                require(d in A and m // d in A, 'nonunit divisor missing')
    witnesses = {m: [primary[m]] for m in A}
    require(isinstance(extra, list) and len(extra) == 8, 'expected eight extra points')
    for row in extra:
        require(set(row) == {'modulus', 'private_point'} and
                all(type(v) is int for v in row.values()), 'invalid extra point')
        require(row['modulus'] in A, 'extra point has an unknown owner')
        witnesses[row['modulus']].append(row['private_point'])
    witness_checks = 0
    for m, points in witnesses.items():
        for w in points:
            require(0 <= w < period, 'witness outside original period')
            require([n for n, a in A.items() if w % n == a] == [m],
                    'a claimed private point has different original owners')
            witness_checks += 1
    hole = originals['hole']
    require(all(hole % m != a for m, a in A.items()), 'original hole is covered')

    all_counts, composite_counts = Counter(), Counter()
    by_prime, exceptional = {}, []
    for p in primes:
        children = []
        for d in sorted(A):
            m, height = d, 0
            while m % p == 0:
                m //= p
                height += 1
            if height and m > 1:
                require(m in A, 'missing original parent')
                center = A[d] % m
                require(center != A[m], 'child contained in old parent')
                children.append((d, m, center, height))
        local = Counter(eligible_children=len(children))
        for left, right in combinations(children, 2):
            d, m, c, e = left
            f, n, b, h = right
            if m == n:
                continue
            counters = [local, all_counts]
            if not is_prime(m) and not is_prime(n):
                counters.append(composite_counts)
            for counter in counters:
                counter['distinct_parent_child_pairs'] += 1
            if (c - b) % gcd(m, n) != 0:
                for counter in counters:
                    counter['incompatible_centers'] += 1
                continue
            for counter in counters:
                counter['compatible_centers'] += 1
            primary_loss = primary[m] % n != b or primary[n] % m != c
            loss = next(((m, w) for w in witnesses[m] if w % n != b), None)
            if loss is None:
                loss = next(((n, w) for w in witnesses[n] if w % m != c), None)
            require(loss is not None, f'unexcluded candidate at prime{p}, children{d},{f}')
            owner, w = loss
            require(w % m != c and w % n != b, 'lost point enters a new parent')
            for counter in counters:
                counter['blocked_by_primary' if primary_loss else 'blocked_by_extra'] += 1
            if not primary_loss:
                removed = {m, n, d, f}
                changed = [(a, r) for a, r in A.items() if a not in removed]
                changed += [(m, c), (n, b)]
                require(len(changed) == 461, 'wrong changed-family size')
                require(not any(w % a == r for a, r in changed),
                        'literal changed family covers the alleged lost point')
                exceptional.append({
                    'prime': p, 'parents': [m, n], 'children': [d, f],
                    'heights': [e, h], 'centers': [c, b],
                    'lost_private_owner': owner, 'lost_integer': w,
                })
        by_prime[p] = dict(local)
    require(all_counts['compatible_centers'] ==
            all_counts['blocked_by_primary'] + all_counts['blocked_by_extra'],
            'incomplete compatible-pair exclusion')
    return {
        'period': period, 'original_count': len(A), 'original_hole': hole,
        'validated_private_points': witness_checks,
        'all_parents': dict(all_counts), 'both_composite': dict(composite_counts),
        'by_prime': by_prime, 'extra_witness_cases': exceptional,
        'unexcluded_compatible_pairs': 0,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--originals', required=True)
    parser.add_argument('--blockers', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    raw = Path(args.originals).read_bytes()
    blocker_raw = Path(args.blockers).read_bytes()
    result = evaluate(json.loads(raw), json.loads(blocker_raw))
    result['originals_sha256'] = hashlib.sha256(raw).hexdigest()
    result['blockers_sha256'] = hashlib.sha256(blocker_raw).hexdigest()
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result['all_parents'], sort_keys=True))
    print('Unexcluded compatible pairs:', result['unexcluded_compatible_pairs'])


if __name__ == '__main__':
    main()
