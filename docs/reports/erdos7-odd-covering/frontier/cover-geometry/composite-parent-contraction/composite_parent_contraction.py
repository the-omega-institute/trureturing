#!/usr/bin/env python3
"""Check literal odd AP families admitting a joint composite-parent contraction.

Derive both contractions, private regions and coverage from the original
numerical APs. Read and write only the explicit --input/--output paths.
No solver, search directory, producer helper or stored result is used.
All checks remain active with Python -O.
"""

import argparse
import hashlib
import json
from math import gcd, isqrt, lcm
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def is_prime(n):
    return n > 1 and all(n % d for d in range(2, isqrt(n) + 1))


def nonunit_divisors(n):
    result = {n}
    for d in range(2, isqrt(n) + 1):
        if n % d == 0:
            result.update((d, n // d))
    return result


def evaluate(fixture):
    fields = {'name', 'prime', 'source', 'parents', 'children', 'originals'}
    require(isinstance(fixture, dict) and set(fixture) == fields,
            'unexpected fixture fields')
    require(isinstance(fixture['name'], str), 'fixture needs a name')
    originals = fixture['originals']
    require(isinstance(originals, list) and bool(originals), 'no originals')
    require(all(isinstance(row, list) and len(row) == 2 and
                all(type(v) is int for v in row) for row in originals),
            'originals must be integer pairs')
    originals = [tuple(row) for row in originals]
    residues = dict(originals)
    require(len(residues) == len(originals), 'duplicate numerical modulus')
    require(originals == sorted(originals), 'originals must be sorted')
    require(all(m > 1 and m % 2 == 1 and 0 <= a < m for m, a in originals),
            'invalid odd nonunit AP')
    period = lcm(*residues)
    p, source = fixture['prime'], fixture['source']
    require(type(p) is int and is_prime(p), 'invalid designated prime')
    require(type(source) is int, 'invalid common source')
    require(period % p == 0 and period % (p * p) != 0,
            'these fixtures require designated-prime height one')
    require(all(a == 0 for m, a in originals if is_prime(m)),
            'original prime classes are not normalized')
    divisor_checks = 0
    for m in residues:
        divisors = nonunit_divisors(m)
        require(divisors <= residues.keys(), 'missing nonunit divisor')
        divisor_checks += len(divisors)
    for i, (m, a) in enumerate(originals):
        for n, b in originals[i + 1:]:
            require(n % m != 0 or b % m != a, 'comparable originals intersect')

    parents, children = fixture['parents'], fixture['children']
    require(isinstance(parents, list) and isinstance(children, list) and
            len(parents) == len(children) == 2, 'expected two pairs')
    require(all(type(m) is int for m in parents + children), 'invalid labels')
    require(len(set(parents + children)) == 4, 'four labels not distinct')
    for m, d in zip(parents, children):
        require(m in residues and d in residues, 'missing parent or child')
        require(not is_prime(m) and gcd(m, p) == 1, 'parent not composite p-free')
        require(d == p * m, 'child is not the stated height-one lift')
        require(residues[d] % m == source % m, 'child misses the common cofactor')
        require(residues[m] != source % m, 'old and new parents coincide')
    require(all(source % m != a for m, a in originals if m % p != 0),
            'source meets a p-free original')
    roots = [residues[d] % p for d in children]
    require(0 not in roots and len(set(roots)) == 2,
            'children need distinct nonzero designated-prime roots')

    removed = set(parents + children)
    retained = [(m, a) for m, a in originals if m not in removed]
    changed = sorted(retained + [(m, source % m) for m in parents])
    require(len(changed) == len(originals) - 2 and
            len({m for m, _ in changed}) == len(changed), 'invalid contraction')
    singles = [[(n, a) for n, a in originals if n not in {m, d}] +
               [(m, source % m)] for m, d in zip(parents, children)]
    private_counts = {m: 0 for m in residues}
    private_witnesses = {}
    single_losses = [[], []]
    old_count = new_count = gained = overlap_count = 0
    joint_count = multiple_owner_count = 0
    multiple_owner_witness = None
    old_hole = new_hole = None
    for x in range(period):
        hits = [m for m, a in originals if x % m == a]
        old = bool(hits)
        new = any(x % m == a for m, a in changed)
        old_count += old
        new_count += new
        gained += new and not old
        require(not old or new, f'joint contraction loses integer {x}')
        if not old and old_hole is None:
            old_hole = x
        if not new and new_hole is None:
            new_hole = x
        if len(hits) == 1:
            m = hits[0]
            private_counts[m] += 1
            private_witnesses.setdefault(m, x)
        if old and set(hits) <= removed:
            joint_count += 1
            if len(hits) > 1:
                multiple_owner_count += 1
                if multiple_owner_witness is None:
                    multiple_owner_witness = {'integer': x, 'old_owners': hits}
        if all(x % m == residues[m] for m in parents):
            overlap_count += 1
            require(any(x % m == a for m, a in retained),
                    'old parent overlap lacks a retained covering class')
        for i, family in enumerate(singles):
            if old and not any(x % m == a for m, a in family):
                single_losses[i].append(x)
    require(all(private_counts.values()), 'an original is redundant')
    require(all(single_losses), 'a single contraction unexpectedly succeeds')
    require(old_hole is not None and new_hole is not None, 'unexpected whole cover')
    require(multiple_owner_count > 0, 'no joint liability beyond individual privacy')

    cofactor_period = period // p
    active_roots = {}
    for root in range(1, p):
        x = (source + cofactor_period *
             ((root - source) * pow(cofactor_period, -1, p) % p)) % period
        active_roots[root] = [m for m, a in originals if x % m == a]
    return {
        'name': fixture['name'], 'period': period,
        'original_count': len(originals), 'new_count': len(changed),
        'divisor_membership_checks': divisor_checks,
        'private_counts': private_counts, 'private_witnesses': private_witnesses,
        'old_covered': old_count, 'new_covered': new_count, 'lost': 0, 'gained': gained,
        'old_holes': period - old_count, 'new_holes': period - new_count,
        'old_hole_witness': old_hole, 'new_hole_witness': new_hole,
        'single_contraction_losses': [len(xs) for xs in single_losses],
        'single_loss_witnesses': [xs[0] for xs in single_losses],
        'old_parent_overlap_all_retained_covered': overlap_count,
        'old_covered_joint_liability': joint_count,
        'joint_liability_with_multiple_old_owners': multiple_owner_count,
        'multiple_owner_witness': multiple_owner_witness,
        'source': source, 'designated_prime': p, 'selected_child_roots': roots,
        'active_nonzero_root_labels': active_roots,
        'all_nonzero_roots_covered_at_source': all(active_roots.values()),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    raw = Path(args.input).read_bytes()
    fixtures = json.loads(raw)
    require(isinstance(fixtures, list) and bool(fixtures),
            'expected a nonempty list of literal control families')
    results = [evaluate(fixture) for fixture in fixtures]
    require(len({result['name'] for result in results}) == len(results),
            'duplicate fixture names')
    output = {'input_sha256': hashlib.sha256(raw).hexdigest(), 'fixtures': results}
    Path(args.output).write_text(json.dumps(output, indent=2, sort_keys=True) + '\n')
    for result in results:
        print(f"{result['name']}: {result['original_count']} -> {result['new_count']} "
              f"classes, lost {result['lost']}, gained {result['gained']}")


if __name__ == '__main__':
    main()
