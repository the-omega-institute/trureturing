#!/usr/bin/env python3
"""Exact controls for the minimum-source law and nine-point flow theorem.
Reusable integral-flow selection and exact arithmetic for report 435.
These controls are not Lean certification.
"""
from collections import Counter, deque
from fractions import Fraction as F
from itertools import combinations
from math import lcm
import json


def need(ok, message):
    if not ok:
        raise AssertionError(message)


COLS = tuple(range(7))
MODULI = (1, 5, 25, 7, 35, 175)


def crt(point):
    r, a, y = point
    return r + 5*a + 25*((y-r-5*a)*2 % 7)


def admissible(source):
    for removed in combinations(COLS, 2):
        good = sum(len({a for rr, a, y in source if rr == r and y not in removed}) >= 3
                   for r in range(1, 5))
        if good < 3:
            return False
    return True


def nine_flow(source):
    graph = {}
    def edge(u, v, c):
        graph.setdefault(u, {})[v] = c
        graph.setdefault(v, {}).setdefault(u, 0)
    for r in range(1, 5):
        edge(('s',), ('r', r), 3)
        for a in range(5):
            edge(('r', r), ('a', r, a), 1)
    for r, a, y in source:
        edge(('a', r, a), ('y', y), 1)
    for y in COLS:
        edge(('y', y), ('t',), 3)
    value = 0
    while True:
        prev = {('s',): None}
        queue = deque([('s',)])
        while queue and ('t',) not in prev:
            u = queue.popleft()
            for v, c in graph[u].items():
                if c and v not in prev:
                    prev[v] = u
                    queue.append(v)
        if ('t',) not in prev:
            break
        v = ('t',)
        while prev[v] is not None:
            u = prev[v]
            graph[u][v] -= 1
            graph[v][u] += 1
            v = u
        value += 1
    selected = [(r, a, y) for r, a, y in source
                if graph[('a', r, a)][('y', y)] == 0]
    need(len(selected) == value, 'flow witness size')
    need(len({(r, a) for r, a, y in selected}) == value, 'leaf cap')
    need(max(Counter(r for r, a, y in selected).values(), default=0) <= 3, 'root cap')
    need(max(Counter(y for r, a, y in selected).values(), default=0) <= 3, 'column cap')
    cut_min = 1000
    for k in range(8):
        for d in combinations(COLS, k):
            rank = sum(min(3, len({a for rr, a, y in source if rr == r and y in d}))
                       for r in range(1, 5))
            cut_min = min(cut_min, 3*(7-k) + rank)
    need(cut_min == value, 'independent cut formula agrees')
    return value, selected[:9]


def main():
    minimum = [(r, a, a) for r in (1, 2, 3) for a in range(5)]
    need(admissible(minimum), 'minimum source admissibility')
    need(len(minimum) == 15, 'minimum example size')
    literals = [crt(p) for p in minimum]
    centered_sums = []
    for z in literals:
        centered_sums.append(sum(sum(z % m == q % m for m in MODULI)**2 for q in literals))
    need(set(centered_sums) == {68}, 'all pointwise dual averages are 68/15')
    caps = {m: max(Counter(z % m for z in literals).values()) for m in MODULI}
    upper = F(sum(caps[lcm(m, n)] for m in MODULI for n in MODULI), 15)
    need(upper == F(68, 15), 'same-law minimum-source cap')
    need(upper < F(46, 9), 'target margin')
    minimum_flow = nine_flow(minimum)

    rows = (((0, 1),)*3, ((0, 2), (0, 3), (0, 2)),
            ((0, 4), (0, 4), (1, 4)), ((0, 5), (0, 5), (1, 5)))
    cut_source = [(r, a, y) for r, row in enumerate(rows, 1)
                  for a, ys in enumerate(row) for y in ys]
    need(admissible(cut_source), 'proper-cut source remains admissible')
    cut_flow = nine_flow(cut_source)
    need(cut_flow[0] >= 9, 'new source has nine-point basis')

    full = [(r, a, y) for r in range(1, 5) for a in range(5) for y in COLS]
    need(admissible(full), 'full source admissible')
    full_flow = nine_flow(full)
    bad_basis = [(r, a, r-1) for r in (1, 2, 3) for a in range(3)]
    need(set(bad_basis) <= set(full), 'bad common basis in an admissible source')
    need(len({(r, a) for r, a, y in bad_basis}) == 9, 'bad basis leaf cap')
    need(max(Counter(r for r, a, y in bad_basis).values()) == 3, 'bad basis root cap')
    need(max(Counter(y for r, a, y in bad_basis).values()) == 3, 'bad basis column cap')
    center = crt((1, 0, 0))
    square = sum(sum(crt(p) % m == center % m for m in MODULI)**2 for p in bad_basis)
    need(F(square, 9) == F(74, 9), 'arbitrary basis can fail target')
    print(json.dumps(dict(minimum_source=minimum, minimum_uniform_value=str(upper),
                          minimum_pointwise_dual_numerators=centered_sums,
                          minimum_flow=minimum_flow, proper_cut_source_flow=cut_flow,
                          full_source_flow=full_flow, bad_basis_value=str(F(square, 9))), indent=2))


if __name__ == '__main__':
    main()
