#!/usr/bin/env python3
"""Exact integer checks for the AP-intersection endgame volume."""

import argparse
import json
from itertools import combinations
from math import gcd


def choose2(n):
    return n * (n - 1) // 2 if n >= 2 else 0


def popcount(mask):
    return bin(mask).count('1')


def is_ap(mask):
    xs = [i for i in range(mask.bit_length()) if mask >> i & 1]
    return bool(xs) and (len(xs) < 3 or
                         len({b - a for a, b in zip(xs, xs[1:])}) == 1)


def long_aps(n):
    result = []
    for d in range(1, (n - 1) // 3 + 1):
        for a in range(n - 3 * d):
            mask = 0
            for b in range(a, n, d):
                mask |= 1 << b
                if b >= a + 3 * d:
                    result.append((mask, d))
    return result


def family_masks(n, c, aps):
    candidates = [mask for mask, _ in aps if not (mask >> c & 1)]

    def visit(group, choices):
        for k, mask in enumerate(choices):
            new_group = group + (mask,)
            yield new_group
            yield from visit(new_group, [x for x in choices[k + 1:] if is_ap(x & mask)])

    yield from visit((), candidates)


def matching(adjacency, right_count):
    owner = [-1] * right_count

    def augment(u, seen):
        for v in adjacency[u]:
            if seen[v]:
                continue
            seen[v] = True
            if owner[v] < 0 or augment(owner[v], seen):
                owner[v] = u
                return True
        return False

    return sum(augment(u, [False] * right_count) for u in range(len(adjacency)))


def phi(n, c, group, aps=None):
    if aps is None:
        aps = long_aps(n)
    assert group and all(not (mask >> c & 1) for mask in group)
    assert all(is_ap(a & b) for a, b in combinations(group, 2))
    hmask = (1 << n) - 1
    for mask in group:
        hmask &= mask
    links = []
    for x, y in combinations((i for i in range(n) if i != c), 2):
        pair = (1 << x) | (1 << y)
        if all(pair & member for member in group):
            links.append(pair)
    eligible = [mask for mask, _ in aps if mask >> c & 1
                and all(is_ap(mask & member) for member in group)]
    edges = [[i for i, pair in enumerate(links)
              if pair & member == pair and not is_ap(pair | (1 << c))]
             for member in eligible]
    nu = matching(edges, len(links))
    value = len(group) + popcount(hmask) + len(links) + len(eligible) - nu
    return {'phi': value, 'g': len(group), 'h': popcount(hmask),
            'L': len(links), 'p': len(eligible), 'nu': nu}


def direct_completion(n, c, group, aps):
    hmask = (1 << n) - 1
    for member in group:
        hmask &= member
    links = [((1 << x) | (1 << y))
             for x, y in combinations((i for i in range(n) if i != c), 2)
             if all(member & ((1 << x) | (1 << y)) for member in group)]
    eligible = [mask for mask, _ in aps if mask >> c & 1
                and all(is_ap(mask & member) for member in group)]
    best = 0
    for choice in range(1 << len(eligible)):
        selected = [eligible[i] for i in range(len(eligible)) if choice >> i & 1]
        available = sum(all(not (pair & q == pair and not is_ap(pair | (1 << c)))
                            for q in selected) for pair in links)
        best = max(best, len(selected) + available)
    return len(group) + popcount(hmask) + best


def mask_of(points):
    return sum(1 << (x - 1) for x in points)


def line_bound(v):
    return 0 if v < 4 else 1 if v == 4 else (v + 1) ** 2 // 4 - 6


def terminal_count(m):
    return sum(m // d - 2 for d in range(1, m // 3 + 1))


def sparse_bound(m, kind):
    if kind == 2:
        return line_bound((m + 1) // 2)
    return sum(line_bound((m + d - 1) // d) for d in range(2, m // 3 + 1))


def coarse_margin(m, length, kind):
    e = m - length
    b = m - (m + kind - 1) // kind
    u = length - (length + kind - 1) // kind
    return (choose2(b) - choose2(b - u) + choose2(e // 2) +
            choose2(e - e // 2) + length - (length + kind - 1) // kind -
            terminal_count(m) - sparse_bound(m, kind))


def sparse_ap_masks(m, kind):
    differences = (2,) if kind == 2 else range(3, m // 3 + 1)
    for d in differences:
        for a in range(1, m - 3 * d + 1):
            for last in range(a + 3 * d, m + 1, d):
                yield sum(1 << (x - 1) for x in range(a, last + 1, d))


def small_mixed_check(m, kind):
    pairs = [(x, y) for x in range(1, m + 1) for y in range(x + 1, m + 1)]
    pair_index = {pair: i for i, pair in enumerate(pairs)}
    through = []
    for d in range(1, m // 3 + 1):
        for k in range(3, m // d + 1):
            qmask = sum(1 << (x - 1) for x in range(d, k * d + 1, d))
            through.append((qmask, 1 << pair_index[((k - 1) * d, k * d)]))
    cores = []
    for a in range(1, m + 1):
        for b in range(a, m + 1):
            length = b - a + 1
            if coarse_margin(m, length, kind) >= 0:
                continue
            imask = ((1 << length) - 1) << (a - 1)
            side = 0
            incident = 0
            for i, (x, y) in enumerate(pairs):
                if y < a or x > b:
                    side |= 1 << i
                if a <= x <= b or a <= y <= b:
                    incident |= 1 << i
            cores.append((length, imask, side, incident))
    least = 10**9
    checked = 0
    for member in sparse_ap_masks(m, kind):
        outside = ((1 << m) - 1) ^ member
        outside_pairs = sum(1 << i for i, (x, y) in enumerate(pairs)
                            if outside >> (x - 1) & 1 and outside >> (y - 1) & 1)
        forbidden = 0
        for qmask, image in through:
            if qmask & member:
                forbidden |= image
        for length, imask, side, incident in cores:
            resource = popcount((side | (outside_pairs & incident)) & ~forbidden)
            margin = resource + length - popcount(imask & member) - sparse_bound(m, kind)
            least = min(least, margin)
            checked += 1
    return checked, least


def sparse_boundary_checks():
    values = [(n, choose2((2 * (n - 1)) // 3) - terminal_count(n - 1) -
               sum(line_bound((n + d - 1) // d) for d in range(2, (n - 1) // 3 + 1)))
              for n in range(48, 300)]
    assert min(values, key=lambda row: row[1]) == (53, 0)
    values = [(n, choose2((n - 1) - ((n - 1) + 3) // 4) - terminal_count(n - 1) -
               sum(line_bound((n + d - 1) // d) for d in range(2, (n - 1) // 3 + 1)))
              for n in range(13, 48)]
    assert min(values, key=lambda row: row[1]) == (14, 4)
    exceptional = []
    for n in range(11, 48):
        m = n - 1
        value = choose2(2 * m // 3) - terminal_count(m) - line_bound((n + 1) // 2) - line_bound((n + 2) // 3)
        if value < 0:
            exceptional.append((n, value))
    assert exceptional == [(11, -4), (13, -2), (14, -3), (15, -1), (17, -6)]
    exact = []
    for n, _ in exceptional:
        m = n - 1
        terminals = [((k - 1) * d, k * d) for d in range(1, m // 3 + 1)
                     for k in range(3, m // d + 1)]
        supplies = []
        for a in range(1, m + 1):
            for k in range(3, (m - a) // 3 + 1):
                member = set(range(a, a + 3 * k + 1, 3))
                outside = set(range(1, m + 1)) - member
                supplies.append(choose2(len(outside)) - sum(x in outside and y in outside
                                                              for x, y in terminals))
        exact.append((n, min(supplies), line_bound((n + 1) // 2) + line_bound((n + 2) // 3)))
    assert exact == [(11, 10, 7), (13, 20, 13), (14, 20, 13),
                     (15, 27, 17), (17, 34, 25)]
    return {'coarse_48_299': [53, 0], 'coarse_step4_13_47': [14, 4],
            'exceptions': exact}


def mixed_boundary_checks():
    results = {}
    for kind in (2, 3):
        large = [(m, min(coarse_margin(m, length, kind)
                         for length in range(1, m + 1))) for m in range(46, 1000)]
        expected = (47, 7) if kind == 2 else (49, 31)
        assert min(large, key=lambda row: row[1]) == expected
        cases = 0
        least = 10**9
        for m in range(4 if kind == 2 else 10, 46):
            count, minimum = small_mixed_check(m, kind)
            cases += count
            if count:
                least = min(least, minimum)
        expected_cases = 224176 if kind == 2 else 138
        assert (cases, least) == (expected_cases, 3), (kind, cases, least)
        results[str(kind)] = {'large_min': list(expected), 'small_cases': cases,
                              'small_min': least}
    return results


def cell_count(left, right):
    return sum(l + r >= 3 for l in range(left + 1) for r in range(right + 1))


def counterexamples():
    group = tuple(mask_of(range(a, b + 1)) for a, b in
                  [(2, 5), (2, 6), (2, 7), (3, 6), (3, 7)])
    row = phi(7, 0, group)
    assert (row['g'], row['h'], row['L'], row['p'], row['nu'], row['phi']) == (5, 3, 13, 5, 5, 21)
    missing = {(1 << (x - 1)) | (1 << (y - 1))
               for x, y in combinations(range(2, 8), 2)
               if any(not (member & ((1 << (x - 1)) | (1 << (y - 1)))) for member in group)}
    eligible = [q for q, _ in long_aps(7) if q & 1 and all(is_ap(q & a) for a in group)]
    covered_missing = {e for e in missing if not is_ap(e | 1)
                       and any(q & e == e for q in eligible)}
    assert len(missing) == len(covered_missing) == 2
    assert row['g'] + row['h'] + row['L'] + min(row['p'], len(covered_missing)) == 23 > 22

    n, c = 25, 13
    full = set(range(2, 24, 3))
    a = set(range(8, 21, 3))
    assert len(full) == 8 and len(a) == 5
    cells = [(l, r) for l in range(7) for r in range(7) if l + r >= 3]
    assert len(cells) == 43
    witnesses = {(u, v) for u, v in combinations(list(range(-6, 0)) + list(range(1, 7)), 2)
                 if gcd(abs(u), abs(v)) == 1 and not is_ap((1 << (c - 1)) |
                    (1 << (c + 2 * u - 1)) | (1 << (c + 2 * v - 1)))}
    assert len(witnesses) == 42 and (-4, 5) in witnesses
    assert all(any(c + 2 * j in a for j in range(-l, r + 1)) for l, r in cells)
    assert len(witnesses - {(-4, 5)}) == 41
    assert phi(n, c - 1, (mask_of(full), mask_of(a)))['phi'] == 236

    maxima = {}
    for c in (3, 4):
        aps = long_aps(10)
        values = [(group, phi(10, c, group, aps)['phi'])
                  for group in family_masks(10, c, aps)]
        maximum = max(value for _, value in values)
        winners = [group for group, value in values if value == maximum]
        expected = mask_of(range(5, 11)) if c == 3 else mask_of((1, 4, 7, 10))
        assert winners == [(expected,)]
        maxima[c + 1] = [len(values), maximum]
    assert maxima == {4: [511, 41], 5: [143, 42]}

    for d in (3, 4):
        n = 3 * d + 1
        member = {1, 1 + d, 1 + 2 * d, n}
        for deleted in range(1, n + 1):
            image = {x - (x > deleted) for x in member if x != deleted}
            if len(image) == 4:
                gaps = [y - x for x, y in zip(sorted(image), sorted(image)[1:])]
                assert len(set(gaps)) > 1
            else:
                assert len(image) == 3

    k = 36
    n, c, u, v = 64 * k + 1, 32 * k + 1, 2 * k + 2, 62 * k - 2
    g = (k + 1) * (k + 2) + (k // 2 + 1) ** 2
    h = 15 * k
    z = choose2(49 * k)
    p = 0
    for d in range(1, (n - 1) // 3 + 1, 2):
        side = 32 * k // d
        a_index = 1 if d % 4 == 1 else 3
        r0 = a_index if c + a_index * d <= v else side + 1
        l0 = 4 - a_index if c - (4 - a_index) * d >= u else side + 1
        p += cell_count(side, side) - cell_count(min(side, l0 - 1), min(side, r0 - 1))
    assert (n, c, g, h, z, p) == (2305, 1153, 1767, 540, 1554966, 1640365)
    t = g + h - n
    margin = z - t - p + (n - 1) // 4
    assert t == 2 and margin == -84825
    return {'false_K_phi': row['phi'], 'R7_6_free_witnesses': 41,
            'centre_maxima': maxima, 'R6_6_margin': margin}


def exhaustive(nmax):
    counts = {}
    for n in range(5, nmax + 1):
        aps = long_aps(n)
        count = 0
        for c in (0, n - 1):
            for group in family_masks(n, c, aps):
                row = phi(n, c, group, aps)
                assert row['phi'] <= choose2(n) + 1, (n, c, group, row)
                count += 1
        counts[n] = count
    if nmax == 8:
        assert counts == {5: 2, 6: 14, 7: 126, 8: 4094}, counts
    return counts


def formula_check():
    counts = {}
    for n in (5, 6):
        aps = long_aps(n)
        count = 0
        for c in range(n):
            for group in family_masks(n, c, aps):
                assert phi(n, c, group, aps)['phi'] == direct_completion(n, c, group, aps)
                count += 1
        counts[n] = count
    assert counts == {5: 2, 6: 16}
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--boundary-nmax', type=int, default=8,
                        help='largest N for endpoint-family exhaustion (5..9; default: 8)')
    parser.add_argument('--threads', type=int, default=1,
                        help='maximum CPU threads (1..12; this integer-only program uses one)')
    try:
        args = parser.parse_args()
        if not 5 <= args.boundary_nmax <= 9 or not 1 <= args.threads <= 12:
            parser.error('boundary-nmax must be 5..9 and threads must be 1..12')
    except SystemExit as exc:
        if exc.code:
            print('RESULT endgame status=fail error=invalid_arguments')
        raise
    try:
        output = {'formula_exhaustive': formula_check(),
                  'boundary_exhaustive': exhaustive(args.boundary_nmax),
                  'sparse_boundary': sparse_boundary_checks(),
                  'mixed_boundary': mixed_boundary_checks(),
                  'counterexamples': counterexamples()}
        print(json.dumps(output, sort_keys=True))
    except Exception as exc:
        print(f'RESULT endgame status=fail error={type(exc).__name__}: {exc}')
        raise SystemExit(1) from exc
    print('RESULT endgame status=ok')


if __name__ == '__main__':
    main()
