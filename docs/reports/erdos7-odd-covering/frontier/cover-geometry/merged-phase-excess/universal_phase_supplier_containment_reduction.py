#!/usr/bin/env python3
"""Exact containment reduction of the 452-class phase-supplier diagnostic.

Deleting a class contained in another preserves the entire covered set.
The remaining family has a single outside point with zero merged excess.
This does not assert union-irredundancy or a universal minimal-cover law.
Only explicit input and output files are accessed.
"""
from argparse import ArgumentParser
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import hashlib
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def contained(smaller, larger):
    """The first residue class is a subset of the second one."""
    m, a = smaller
    n, b = larger
    return m > n and m % n == 0 and a % n == b


def retained_part(m):
    d, b, weight = 1, m, Q(1)
    for p in (3, 5, 7):
        power = 1
        while b % p == 0:
            d *= p
            b //= p
            power *= p
        if power > 1:
            weight *= Q(p - 1, (p - 2) * power)
    return d, b, weight


def phases_at(family, y):
    phases, weights = {}, {}
    for m, a in family:
        d, b, weight = retained_part(m)
        if d == 1:
            require(y % b != a % b, 'one common outside survivor')
            continue
        phases.setdefault(d, set())
        weights[d] = weight
        if y % b == a % b:
            phases[d].add(a % d)
    fs = sum((weights[d] * max(len(rs) - 1, 0)
              for d, rs in phases.items()), Q(0))
    fh = sum((Q(max(len(rs) - 1, 0), d)
              for d, rs in phases.items()), Q(0))
    return phases, fs, fh


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    require(args.input.resolve() != args.output.resolve(), 'distinct paths')
    raw = args.input.read_bytes()
    data = json.loads(raw)
    require(set(data) == {'originals'}, 'numerical original-pair input')
    originals = [(r['modulus'], r['residue']) for r in data['originals']]
    require(len(originals) == 452, 'specified original family size')
    require(len({m for m, a in originals}) == 452, 'distinct numerical labels')
    require(all(type(m) is int and type(a) is int and m > 1 and m % 2
                and 0 <= a < m for m, a in originals), 'legal original classes')
    kept = sorted(p for p in originals if not any(contained(p, q) for q in originals))
    witnesses = []
    for p in originals:
        if p in kept:
            continue
        options = [q for q in kept if contained(p, q)]
        require(bool(options), 'every removed class has a retained container')
        witnesses.append({'removed': p, 'retained_container': min(options)})
    require(len(kept) == 263 and len(witnesses) == 189, 'exact containment inventory')
    require(not any(contained(p, q) for p in kept for q in kept), 'containment-free remainder')
    outside = sorted((m, a) for m, a in kept if retained_part(m)[0] == 1)
    require(outside == [(p, 0) for p in (11, 13, 17, 19)], 'unchanged outside-only family')
    y = 24950
    require(0 <= y < prod((11, 13, 17, 19)), 'literal outside coordinate')
    before, before_fs, before_fh = phases_at(originals, y)
    after, after_fs, after_fh = phases_at(kept, y)
    require(before_fs > Q(1, 3) and before_fh > Q(5, 48), 'original excess at same point')
    require(all(len(rs) <= 1 for rs in after.values()), 'one retained phase per original numerical row')
    require(after_fs == after_fh == 0, 'both reduced excesses vanish')
    hole = 64366265250
    require(all(hole % m != a for m, a in originals), 'original literal hole')
    result = {
        'status': 'PASS',
        'scope': 'One union-preserving containment reduction. No claim of union-irredundancy or unrestricted noncoverage.',
        'input_sha256': hashlib.sha256(raw).hexdigest(),
        'original_count': len(originals), 'retained_count': len(kept),
        'removed_count': len(witnesses), 'outside_coordinate': y,
        'outside_coordinates': [y % p for p in (11, 13, 17, 19)],
        'original_FS_at_y': str(before_fs), 'original_FH_at_y': str(before_fh),
        'reduced_FS_at_y': str(after_fs), 'reduced_FH_at_y': str(after_fh),
        'reduced_global_minimum_FS': '0', 'reduced_global_minimum_FH': '0',
        'minimum_justification': 'Every summand is nonnegative and both values are zero at the displayed common outside point.',
        'retained_originals': [{'modulus': m, 'residue': a} for m, a in kept],
        'containment_witnesses': witnesses,
        'retained_phases_at_y': [{'modulus': d, 'phases': sorted(rs)} for d, rs in sorted(after.items())],
    }
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('retained_originals', 'containment_witnesses', 'retained_phases_at_y')}))


if __name__ == '__main__':
    main()
