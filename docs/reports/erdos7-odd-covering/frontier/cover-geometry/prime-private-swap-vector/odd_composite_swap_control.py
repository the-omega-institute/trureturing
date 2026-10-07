#!/usr/bin/env python3
"""Complete ownership control for an odd, divisor-closed noncover.

The unchanged covered set still omits 370 residues. This tests local
conjugacy/descent shortcuts, not whole-cover minimality or Erdős #7.
All checks remain active with Python -O. Standard library only.
"""
from functools import reduce
from math import gcd
import json

from prime_private_swap_vector import check, prepare


ORIGINAL = ((0, 3), (0, 5), (0, 7), (2, 9), (1, 15), (16, 21),
            (4, 25), (1, 35), (32, 45), (17, 63), (2, 105), (3, 175))


def divisors(n):
    return {d for d in range(1, n + 1) if n % d == 0}


def hull(points, period):
    check(bool(points), 'empty private region')
    w = min(points)
    return reduce(gcd, (abs(x - w) for x in points), period)


def run():
    old = prepare(ORIGINAL, require_irredundant=False)
    residues = dict(old['residues'])
    residues[35], residues[105] = 2, 71
    new = prepare(tuple((a, n) for n, a in residues.items()),
                  require_irredundant=False)
    period, labels = old['period'], set(residues)
    check(period == new['period'] == 1575, 'wrong full period')
    check(all(n > 1 and n % 2 for n in labels), 'odd nonunit labels')
    check(not old['missing_divisors'] and not new['missing_divisors'],
          'divisor closure')
    check(old['comparable'] and new['comparable'], 'comparable disjointness')
    po, pn = old['private'], new['private']
    check(all(po.values()) and all(pn.values()), 'original private points')
    covered = {x for x, owners in enumerate(old['labels']) if owners}
    check(covered == {x for x, owners in enumerate(new['labels']) if owners},
          'covered sets differ')
    check(period - len(covered) == 370, 'noncover complement size')
    check(not old['labels'][8] and not new['labels'][8], 'uncovered witness')

    def ap(n, a):
        return {x for x in range(period) if x % n == a % n}

    check(po[35] == ap(315, 71) | ap(315, 176), 'complete old parent private')
    check(po[105] == ap(315, 107), 'complete old child private')
    check(pn[35] == po[105] and pn[105] == po[35], 'private transport')
    check(71 in po[35] and 107 in po[105], 'same-source private witnesses')
    check(residues[35] == 107 % 35 and residues[105] == 71 % 105,
          'prescribed swap phases')

    e_minus = old['classes'][35] - new['classes'][105]
    e_plus = new['classes'][35] - old['classes'][105]
    check(not e_minus & e_plus, 'shells intersect')
    for n in labels - {35, 105}:
        loss = po[n] & e_plus
        gain = {x for x in e_minus if old['labels'][x] == {35, n}}
        check(pn[n] == (po[n] - loss) | gain, 'complete third-label update')
        check(not (po[n] - loss) & gain, 'gain/loss union not disjoint')
    for a, owners in [(1, {35, 15}), (36, {35, 3}), (37, {21}), (72, {3})]:
        check(all(old['labels'][x] == owners for x in ap(105, a)),
              'full shell ownership')

    thresholds = {d: max(n for n in labels if n % d == 0) for d in labels}
    closure = []
    for name, points in [('old', po), ('new', pn)]:
        for n in sorted(labels):
            h = hull(points[n], period)
            demanded = {e for e in divisors(h) if 1 < e < thresholds[n]}
            check(demanded <= labels, 'missing label below encloser threshold')
            closure.append(dict(state=name, label=n, hull=h,
                                threshold=thresholds[n],
                                required_occupied=sorted(demanded)))

    check(gcd(35, 15, old['residues'][35] - old['residues'][15]) == 5,
          'old signature')
    check(gcd(35, 15, residues[35] - residues[15]) == 1, 'new signature')
    check(thresholds[35] == 175 and thresholds[105] == 105, 'price gap')
    child_divisors = divisors(hull(po[105], period))
    check(not {e for e in child_divisors if 105 < e < 175}, 'gap divisor')
    check(min(child_divisors - labels - {1}) == 315, 'first missing encloser')
    check(all(n == 105 or residues[n] % 35 != residues[35]
              for n in labels - {35} if n % 35 == 0), 'parent receiver')
    check(not {n for n in labels - {105} if n % 105 == 0}, 'child receiver')
    table = [dict(label=n, residue=[old['residues'][n], residues[n]],
                  private_count=[len(po[n]), len(pn[n])],
                  hull=[hull(po[n], period), hull(pn[n], period)])
             for n in sorted(labels)]
    return dict(period=period, uncovered_count=period - len(covered),
                common_uncovered_witness=8, table=table, closure=closure,
                scope='finite noncover; no whole-cover minimality')


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
