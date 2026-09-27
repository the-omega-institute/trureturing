#!/usr/bin/env python3
"""Finite role orbit census under the fixed low-pure/15-mask stabilizer.

Ordinary exact finite check only; no full layout or gate enumeration.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json


def require(condition, name):
    if not condition:
        raise ArithmeticError(name)


def swap(value, a, b):
    return b if value == a else a if value == b else value


def neighbors(t):
    r, s, ell = t
    for a, b in ((0, 1), (1, 2), (4, 5), (6, 7), (7, 8)):
        yield r, s, swap(ell, a, b)
    yield r, swap(s, 2, 3), ell


def orbits(domain, expected_count):
    remaining = set(domain)
    result = []
    while remaining:
        start = min(remaining)
        seen = {start}
        todo = [start]
        while todo:
            current = todo.pop()
            for nxt in neighbors(current):
                require(nxt in domain, 'domain invariant under generators')
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
        remaining.difference_update(seen)
        result.append(sorted(seen))
    require(len(result) == expected_count, 'orbit count')
    require(sum(map(len, result)) == len(domain), 'orbit total')
    require(len(set(t for orbit in result for t in orbit)) == len(domain), 'disjoint cover')
    return result


domains = {
    'full': (set(product(range(3), range(5), range(9))), 48),
    'padded': (set(product(range(2), range(4), range(6))), 18),
    'live': (set(product(range(2), range(4), (0, 1, 2, 4, 5))), 12),
}
output = {}
for name, (domain, expected) in domains.items():
    os = orbits(domain, expected)
    output[name] = {
        'triple_count': len(domain),
        'orbit_count': len(os),
        'size_histogram': dict(sorted(Counter(map(len, os)).items())),
        'orbits': os,
    }

baseline_orbit = next(orbit for orbit in output['live']['orbits'] if (1, 2, 5) in orbit)
require(baseline_orbit == [(1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5)], 'baseline orbit')


def unary(role, cell):
    r, s, ell = role
    l, m = cell
    n = int(l // 3 == r) + int(m // 5 == s) + int(l == ell)
    return Fraction(5, 6) - Fraction(n, 35)


cross = []
for cell in ((0, 6), (4, 6)):
    left = unary((0, 2, 5), cell)
    right = unary((1, 2, 5), cell)
    cross.append({'cell': cell, 'r0_mass': str(left), 'r1_mass': str(right)})
require(Fraction(cross[0]['r0_mass']) < Fraction(cross[0]['r1_mass']), 'first crossing')
require(Fraction(cross[1]['r0_mass']) > Fraction(cross[1]['r1_mass']), 'second crossing')
output.update(status='PASS', baseline_orbit=baseline_orbit, unary_crossing=cross,
              new_lean_verification=False)
destination = Path(__file__).with_suffix('.json')
destination.write_text(json.dumps(output, indent=2) + '\n')
print(json.dumps({name: {k: value for k, value in output[name].items() if k != 'orbits'}
                  for name in domains}, indent=2))
print(json.dumps({'status': 'PASS', 'baseline_orbit': baseline_orbit,
                  'unary_crossing': cross}, indent=2))
