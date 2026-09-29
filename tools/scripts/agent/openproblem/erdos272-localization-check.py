#!/usr/bin/env python3
"""Verify localization thresholds and two-line AP bounds by exact counting."""

import argparse
import json
import os
from functools import lru_cache
from itertools import combinations
from fractions import Fraction
from math import inf

for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS',
            'VECLIB_MAXIMUM_THREADS'):
    os.environ[key] = '1'

from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def f(m):
    if m < 4:
        return 0
    if m == 4:
        return 1
    return ((m + 1) * (m + 1)) // 4 - 6


def ap_bound(n):
    return sum(f((n + d - 1) // d) for d in range(1, (n - 1) // 3 + 1))


def b(n):
    return n * (n - 1) // 2 + 1 + (n - 1) // 4


def admissible_small(n):
    a = n // 12
    return ap_bound(n) + n - 1 + a * (n - 1) - a * (a + 1) // 2 <= b(n)


def admissible_large_difference(n):
    a = (n - 1) // 13 + 1
    return ap_bound(n) + n - 1 + a * (n - 1) - a * (a + 1) // 2 <= b(n)


def audit(nmin=13, nmax=8191):
    tests = {
        "triples_not_star": lambda n: ap_bound(n) + (n - 1) + (3 * n - 8) <= b(n),
        "avoiding_pair": lambda n: ap_bound(n) + (n - 1) + (2 * n - 3) <= b(n),
        "length_gt_N_over_12": admissible_small,
        "difference_at_most_12": lambda n: n // 12 > (n - 1) // 13,
        "direct_difference_at_most_12": admissible_large_difference,
    }
    failures = {}
    for name, predicate in tests.items():
        bad = [n for n in range(nmin, nmax + 1) if not predicate(n)]
        failures[name] = max(bad) if bad else None
    if nmin == 13 and nmax >= 242:
        assert failures['triples_not_star'] == 41
        assert failures['avoiding_pair'] == 26
        assert failures['length_gt_N_over_12'] == 241
        assert failures['direct_difference_at_most_12'] == 171
    return failures


def brute_f():
    for m in range(1, 31):
        actual = max(sum(1 for a in range(1, p + 1)
                         for z in range(p, m + 1) if z - a + 1 >= 4)
                     for p in range(1, m + 1))
        assert actual == f(m), (m, actual, f(m))
    print("interval formula checked for M=1..30")


def is_ap(mask):
        xs = [i for i in range(mask.bit_length()) if mask >> i & 1]
        return len(xs) < 3 or len(set(xs[i + 1] - xs[i] for i in range(len(xs) - 1))) == 1


def brute_private(nmax=9):
    checked = 0
    for n in range(4, nmax + 1):
        for mask in range(1, 1 << n):
            xs = [i for i in range(n) if mask >> i & 1]
            if len(xs) < 4 or is_ap(mask):
                continue
            witnesses = []
            for i in range(len(xs) - 2):
                t = sum(1 << x for x in xs[i:i + 3])
                if not is_ap(t):
                    witnesses.append(t)
            assert witnesses
            for t in witnesses:
                for other in range(1, 1 << n):
                    if other == mask or other & t != t:
                        continue
                    assert not is_ap(other & mask), (n, xs, t, other)
            checked += 1
    print("private-consecutive-triple check on", checked, "non-AP sets through N=", nmax)


def brute_helly(nmax=9):
    checked = 0
    for n in range(4, nmax + 1):
        lines = {}
        for d in range(1, (n - 1) // 3 + 1):
            for a in range(n - 3 * d):
                mask = 0
                for x in range(a, n, d):
                    mask |= 1 << x
                    if x >= a + 3 * d:
                        lines.setdefault(d, []).append(mask)
        for aps in lines.values():
            for a, b, c in combinations(aps, 3):
                if a & b and a & c and b & c:
                    assert a & b & c
                    checked += 1
    print("same-d Helly checked on", checked, "pairwise-intersecting AP triples through N=", nmax)


def rational_tail():
    zeta_upper = sum((Fraction(1, d * d) for d in range(1, 21)), Fraction()) + Fraction(1, 20)
    assert zeta_upper < Fraction(33, 20)
    coefficient = Fraction(33, 80) + Fraction(1, 512) + Fraction(1, 12)
    assert coefficient == Fraction(3823, 7680)
    assert (Fraction(1, 2) - coefficient) * 8192 - Fraction(11, 6) > 0
    basic_coefficient = Fraction(33, 80) + Fraction(1, 512)
    assert (Fraction(1, 2) - basic_coefficient) * 8192 - Fraction(29, 6) > 0
    assert (Fraction(1, 2) - basic_coefficient) * 8192 - Fraction(23, 6) > 0
    difference_coefficient = Fraction(33, 80) + Fraction(1, 512) + Fraction(1, 13)
    assert (Fraction(1, 2) - difference_coefficient) * 8192 - Fraction(17, 6) > 0
    print("rational tail certified from N=8192, coefficient", coefficient)


def brute_links(nmax=9):
    checked = 0
    for n in range(4, nmax + 1):
        for a in range(1, n):
            hits = sum(bool((x < a) or (y < a)) for x, y in combinations(range(n - 1), 2))
            assert hits == a * (n - 1) - a * (a + 1) // 2
            checked += 1
    print("link-pair counts checked for", checked, "(N,a) values through N=", nmax)


def brute_hilton_milner():
    for n in (7, 8):
        triples = [sum(1 << x for x in xs) for xs in combinations(range(n), 3)]
        rows, cols, data, lo, hi = [], [], [], [], []
        for i, j in combinations(range(len(triples)), 2):
            if triples[i] & triples[j]:
                continue
            row = len(lo)
            rows.extend((row, row))
            cols.extend((i, j))
            data.extend((1, 1))
            lo.append(0)
            hi.append(1)
        for x in range(n):
            row = len(lo)
            indices = [i for i, t in enumerate(triples) if not t >> x & 1]
            rows.extend(row for _ in indices)
            cols.extend(indices)
            data.extend(1 for _ in indices)
            lo.append(1)
            hi.append(inf)
        matrix = coo_matrix((data, (rows, cols)),
                            shape=(len(lo), len(triples))).tocsr()
        result = milp([-1] * len(triples), integrality=[1] * len(triples),
                      bounds=Bounds([0] * len(triples), [1] * len(triples)),
                      constraints=LinearConstraint(matrix, lo, hi),
                      options={"mip_rel_gap": 0.0})
        assert result.status == 0 and round(-result.fun) == 3 * n - 8
        print("nonstar intersecting triple maximum at N=", n, "is", round(-result.fun))


def line_candidates(n):
    groups = {}
    for d in range(1, (n - 1) // 3 + 1):
        aps = []
        for a in range(n - 3 * d):
            mask = 0
            for x in range(a, n, d):
                mask |= 1 << x
                if x >= a + 3 * d:
                    aps.append(mask)
        groups[d] = [tuple(ap for ap in aps if ap >> p & 1) for p in range(n)]
    return groups


def matching(left, right):
    if len(left) > len(right):
        left, right = right, left
    adjacency = [[j for j, b in enumerate(right) if not a & b] for a in left]
    owner = [-1] * len(right)

    def augment(i, seen):
        for j in adjacency[i]:
            if seen[j]:
                continue
            seen[j] = True
            if owner[j] < 0 or augment(owner[j], seen):
                owner[j] = i
                return True
        return False

    return sum(augment(i, [False] * len(right)) for i in range(len(left)))


def pair_max(first, second):
    best = max(len(first[p]) + len(second[p]) for p in range(len(first)))
    for a in first:
        for b in second:
            raw = len(a) + len(b)
            if raw > best:
                best = max(best, raw - matching(a, b))
    return best


def pair_bound(n):
    groups = line_candidates(n)
    ds = tuple(groups)
    maxima = {d: max(map(len, groups[d])) for d in ds}
    savings = {}
    for d, e in combinations(ds, 2):
        savings[d, e] = maxima[d] + maxima[e] - pair_max(groups[d], groups[e])

    @lru_cache(None)
    def best(mask):
        if mask == 0:
            return 0
        bit = mask & -mask
        i = bit.bit_length() - 1
        rest = mask ^ bit
        return max([best(rest)] + [savings[ds[i], ds[j]] + best(rest ^ (1 << j))
                                   for j in range(i + 1, len(ds)) if rest >> j & 1])

    upper = sum(maxima.values()) - best((1 << len(ds)) - 1)
    cap = b(n) - 4 * n + 9
    assert (upper <= cap) == (n != 37), (n, upper, cap)
    return {'upper': upper, 'cap': cap}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmin', type=int, default=13,
                        help='first N for exact localization checks (13..8191)')
    parser.add_argument('--nmax', type=int, default=8191,
                        help='last N for exact localization checks (13..8191)')
    parser.add_argument('--pair-nmin', type=int, default=36,
                        help='first N for two-line bounds (36..41)')
    parser.add_argument('--pair-nmax', type=int, default=41,
                        help='last N for two-line bounds (36..41)')
    parser.add_argument('--threads', type=int, default=1,
                        help='maximum CPU threads (1..12; counting and small MILPs use one)')
    try:
        args = parser.parse_args()
        if not (13 <= args.nmin <= args.nmax <= 8191 and
                36 <= args.pair_nmin <= args.pair_nmax <= 41 and
                1 <= args.threads <= 12):
            parser.error('invalid range or thread count')
    except SystemExit as exc:
        if exc.code:
            print('RESULT localization status=fail error=invalid_arguments')
        raise
    try:
        brute_f()
        brute_private()
        brute_helly()
        brute_links()
        brute_hilton_milner()
        rational_tail()
        failures = audit(args.nmin, args.nmax)
        pair_bounds = {n: pair_bound(n) for n in range(args.pair_nmin,
                                                        args.pair_nmax + 1)}
        if args.pair_nmin == 36 and args.pair_nmax == 41:
            assert [pair_bounds[n]['upper'] for n in range(36, 42)] == [500, 541, 564, 599, 627, 670]
        print(json.dumps({'last_failures': failures, 'pair_bounds': pair_bounds}, sort_keys=True))
    except Exception as exc:
        print(f'RESULT localization status=fail error={type(exc).__name__}: {exc}')
        raise SystemExit(1) from exc
    print('RESULT localization status=ok')


if __name__ == '__main__':
    main()
