#!/usr/bin/env python3
"""Exclude every size of same-prime centered parent relocation in the463 family.

Read only explicit input paths. Reconstruct all original child options and
validate every private integer. Necessary rescue constraints are propagated
without enumerating subsets or bounding their size. Checks survive -O.
"""

import argparse
import hashlib
import json
from math import gcd, isqrt, lcm
from pathlib import Path


ORIGINALS_SHA256 = '427138d17d61f284dff84c2143b90b3b5b3997af6c26e9a8c17f4ab790aa1e11'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def prime_factors(n):
    factors = {}
    divisor = 2
    while divisor * divisor <= n:
        while n % divisor == 0:
            factors[divisor] = factors.get(divisor, 0) + 1
            n //= divisor
        divisor += 1
    if n > 1:
        factors[n] = 1
    return factors


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask -= bit


def child_options(classes, prime):
    grouped = {}
    for child, residue in sorted(classes.items()):
        parent, height = child, 0
        while parent % prime == 0:
            parent //= prime
            height += 1
        if height == 0 or parent == 1:
            continue
        require(parent in classes, 'missing original cofactor parent')
        center = residue % parent
        require(center != classes[parent], 'old parent contains its child')
        grouped.setdefault((parent, center), []).append((child, height))
    return [(parent, center, tuple(children))
            for (parent, center), children in sorted(grouped.items())]


def exclude_options(options, witnesses):
    """Return the remaining necessary-condition core, not a feasible exchange.

    Every legal selected set stays inside each global live set. Conditional
    peeling assumes one seed is selected and restricts to its compatible
    neighbors. A seed deleted there cannot belong to any legal selected set.
    """
    compatible = []
    requirements = []
    for i, (parent, center, _) in enumerate(options):
        mask = 1 << i
        for j, (other, phase, _) in enumerate(options):
            if other != parent and (center - phase) % gcd(parent, other) == 0:
                mask |= 1 << j
        compatible.append(mask)
        rows = []
        for point in witnesses[parent]:
            rescuers = 0
            for j in indices(mask & ~(1 << i)):
                other, phase, _ = options[j]
                if point % other == phase:
                    rescuers |= 1 << j
            rows.append((point, rescuers))
        require(rows, 'parent has no checked private witness')
        requirements.append(rows)

    used = set()
    deletion_checks = 0

    def peel(universe):
        nonlocal deletion_checks
        live = universe
        layers = []
        while live:
            deleted = []
            for i in indices(live):
                for point, rescuers in requirements[i]:
                    if rescuers & live == 0:
                        deleted.append(i)
                        used.add((options[i][0], point))
                        break
            if not deleted:
                break
            layers.append(len(deleted))
            deletion_checks += len(deleted)
            for i in deleted:
                live &= ~(1 << i)
        return live, layers

    live, plain_layers = peel((1 << len(options)) - 1)
    after_plain = live.bit_count()
    conditional_passes = []
    while live:
        rejected = []
        attempted = live.bit_count()
        for seed in indices(live):
            residual, _ = peel(live & compatible[seed])
            if residual & (1 << seed) == 0:
                rejected.append(seed)
        if not rejected:
            break
        for seed in rejected:
            live &= ~(1 << seed)
        live, followup_layers = peel(live)
        conditional_passes.append({
            'seeds_tested': attempted,
            'seeds_excluded': len(rejected),
            'plain_followup_layers': followup_layers,
            'remaining': live.bit_count(),
        })
    return {
        'option_count': len(options),
        'original_child_count': sum(len(children) for _, _, children in options),
        'plain_layers': plain_layers,
        'remaining_after_plain': after_plain,
        'conditional_passes': conditional_passes,
        'remaining': live.bit_count(),
        'checked_deletions': deletion_checks,
        'private_points_used': len(used),
    }


def evaluate(originals, blockers):
    require(blockers['input_sha256'] == ORIGINALS_SHA256, 'wrong witness source')
    rows = originals['originals']
    require(len(rows) == 463, 'expected463 originals')
    require(all(type(row[key]) is int for row in rows
                for key in ('modulus', 'residue', 'private_point')), 'noninteger original')
    classes = {row['modulus']: row['residue'] for row in rows}
    require(len(classes) == len(rows), 'duplicate numerical modulus')
    require(all(m > 1 and m % 2 == 1 and 0 <= a < m for m, a in classes.items()),
            'invalid original odd AP')
    period = lcm(*classes)
    require(period == 481225870125, 'unexpected original period')
    primes = sorted({p for m in classes for p in prime_factors(m)})
    require(primes == [3, 5, 7, 11, 13, 17, 19], 'unexpected support')
    require(all(classes.get(p) == 0 for p in primes), 'prime normalization fails')
    for m in classes:
        for divisor in range(2, isqrt(m) + 1):
            if m % divisor == 0:
                require(divisor in classes and m // divisor in classes,
                        'nonunit divisor missing')
    witnesses = {row['modulus']: [row['private_point']] for row in rows}
    require(len(blockers['rows']) == 395, 'expected395 additional private integers')
    for row in blockers['rows']:
        require(set(row) == {'modulus', 'private_point'} and
                all(type(value) is int for value in row.values()), 'invalid witness row')
        m, point = row['modulus'], row['private_point']
        require(m in witnesses and point not in witnesses[m], 'duplicate or unknown witness')
        witnesses[m].append(point)
    witness_count = 0
    for m, points in witnesses.items():
        for point in points:
            require(0 <= point < period, 'private integer outside period')
            require([d for d, a in classes.items() if point % d == a] == [m],
                    'claimed private integer has different original owners')
            witness_count += 1
    require(all(originals['hole'] % m != a for m, a in classes.items()),
            'the original hole is covered')

    results = []
    for prime in primes:
        result = exclude_options(child_options(classes, prime), witnesses)
        result['prime'] = prime
        require(result['remaining'] == 0, f'prime{prime} has unexcluded options')
        results.append(result)
    return {
        'period': period,
        'original_count': len(classes),
        'original_hole': originals['hole'],
        'validated_private_points': witness_count,
        'original_membership_checks': witness_count * len(classes),
        'option_count': sum(row['option_count'] for row in results),
        'checked_deletions': sum(row['checked_deletions'] for row in results),
        'by_prime': results,
        'all_same_prime_batches_excluded': True,
        'scope': 'Any nonempty batch of distinct cofactor parents, with one fixed '
                 'prime and actual child-induced centers sharing a common CRT point; '
                 'even retaining every child cannot preserve the old covered union.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--originals', required=True)
    parser.add_argument('--blockers', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    raw = Path(args.originals).read_bytes()
    blocker_raw = Path(args.blockers).read_bytes()
    require(hashlib.sha256(raw).hexdigest() == ORIGINALS_SHA256, 'wrong original input bytes')
    result = evaluate(json.loads(raw), json.loads(blocker_raw))
    result['originals_sha256'] = ORIGINALS_SHA256
    result['blockers_sha256'] = hashlib.sha256(blocker_raw).hexdigest()
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({key: result[key] for key in
                      ('option_count', 'validated_private_points', 'checked_deletions',
                       'all_same_prime_batches_excluded')}, sort_keys=True))


if __name__ == '__main__':
    main()
