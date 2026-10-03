#!/usr/bin/env python3
"""Finite checks for the matching-with-one-shared-edge CFMP continuation.

Python standard library only. The written proof establishes the unbounded
statements. Floating tests are not interval certificates or Lean proofs.
Local edge order: (01,02,03,23,13,12). Every face entry is (t,f,u,g,p),
where f and g are omitted vertices and p maps source vertices to target ones.
"""
from __future__ import annotations

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
import json
import math
import random

EDGES = ((0, 1), (0, 2), (0, 3), (2, 3), (1, 3), (1, 2))
INDEX = {edge: i for i, edge in enumerate(EDGES)}
PI = math.pi

TABLE_SIX = """
3 0 4 2 2310
4 3 0 3 1023
0 2 3 2 1023
3 3 2 1 3201
2 0 5 2 2310
5 3 3 1 3201
0 1 9 2 3201
9 3 7 3 1023
7 2 6 3 0132
6 2 8 2 1023
8 3 1 3 1023
1 2 0 0 3201
10 3 1 1 3201
1 0 2 3 3201
2 2 13 2 1023
13 3 12 2 0132
12 3 11 2 0132
11 3 10 2 0132
7 0 4 0 0213
10 1 8 1 0132
9 1 7 1 3120
9 0 11 0 0213
13 1 13 0 2031
5 1 4 1 3120
5 0 11 1 1230
12 1 8 0 3012
10 0 6 0 0132
6 1 12 0 3012
"""

TABLE_FOUR = """
3 3 2 1 3201
2 0 0 2 2310
0 3 3 0 2310
3 1 3 2 3201
0 0 4 3 3201
4 2 1 3 0132
1 2 5 2 1023
5 3 0 1 3201
1 1 7 3 2310
7 2 6 2 1023
6 3 2 3 1023
2 2 1 0 3201
4 1 6 1 2103
4 0 7 0 0132
5 1 7 1 3120
5 0 6 0 0132
"""


class DisjointSets:
    def __init__(self, size: int) -> None:
        self.parent = list(range(size))

    def find(self, item: int) -> int:
        while self.parent[item] != item:
            self.parent[item] = self.parent[self.parent[item]]
            item = self.parent[item]
        return item

    def union(self, first: int, second: int) -> None:
        self.parent[self.find(first)] = self.find(second)

    def groups(self) -> list[list[int]]:
        groups: dict[int, list[int]] = {}
        for item in range(len(self.parent)):
            groups.setdefault(self.find(item), []).append(item)
        return sorted(groups.values())


def verify_packet(table: str, n: int, special_degree: int) -> dict[str, object]:
    """Check actual gluing, not only proposed labels or Euler characteristic."""
    rows = []
    for line in table.strip().splitlines():
        t, f, u, g, word = line.split()
        rows.append((int(t), int(f), int(u), int(g), tuple(map(int, word))))
    faces: dict[tuple[int, int], tuple[int, int, tuple[int, ...]]] = {}
    vertices, edges, blocks = DisjointSets(4*n), DisjointSets(6*n), DisjointSets(n)
    flags = {(t, i, j): [] for t in range(n)
             for i in range(4) for j in range(4) if i != j}
    for t, f, u, g, p in rows:
        assert 0 <= t < n and 0 <= u < n
        assert sorted(p) == [0, 1, 2, 3] and p[f] == g
        assert sum(p[i] > p[j] for i in range(4) for j in range(i+1, 4)) % 2 == 1
        assert (t, f) != (u, g)
        assert (t, f) not in faces and (u, g) not in faces
        faces[t, f] = (u, g, p)
        faces[u, g] = (t, f, tuple(p.index(i) for i in range(4)))
        blocks.union(t, u)
        face_vertices = [i for i in range(4) if i != f]
        for i in face_vertices:
            vertices.union(4*t+i, 4*u+p[i])
        for i, j in combinations(face_vertices, 2):
            edges.union(6*t+INDEX[i, j], 6*u+INDEX[tuple(sorted((p[i], p[j])))])
        for i, j in permutations(face_vertices, 2):
            a, b = (t, i, j), (u, p[i], p[j])
            flags[a].append(b)
            flags[b].append(a)
    assert len(faces) == 4*n and len(blocks.groups()) == 1
    groups = edges.groups()
    assert len(groups) == 4
    label = {o: j for j, group in enumerate(groups) for o in group}
    degrees = [len(group) for group in groups]
    reservoir = label[1]
    assert degrees[reservoir] == 6*n-3*special_degree
    assert sorted(degrees) == [special_degree]*3+[6*n-3*special_degree]
    local = [[label[6*t+j] for j in range(6)] for t in range(n)]
    assert local[0][0] != local[0][3]
    assert local[3][0] == local[3][3] != reservoir  # genuine repeated label
    interaction_pairs = []
    for row in local:
        special_slots = [j for j in range(6) if row[j] != reservoir]
        assert len(special_slots) <= 2
        if len(special_slots) == 2:
            i, j = special_slots
            assert not set(EDGES[i]) & set(EDGES[j])
            interaction_pairs.append(tuple(sorted((row[i], row[j]))))
    special_labels = sorted(set(label.values())-{reservoir})
    assert all(tuple(pair) in interaction_pairs for pair in combinations(special_labels, 2))
    assert sum(a == b for a, b in interaction_pairs) == 1
    # Each normal walk remembers ordered endpoints and the incoming face.
    circles = []
    for group in groups:
        t, slot = divmod(min(group), 6)
        a, b = EDGES[slot]
        entry = next(v for v in range(4) if v not in (a, b))
        first = state = (t, a, b, entry)
        visited = []
        for step in range(len(group)):
            t, a, b, entry = state
            visited.append(6*t+INDEX[tuple(sorted((a, b)))])
            exit_face = next(v for v in range(4) if v not in (a, b, entry))
            u, g, p = faces[t, exit_face]
            state = (u, p[a], p[b], g)
            assert state != first or step == len(group)-1
        assert state == first and sorted(visited) == group
        circles.append(visited)
    # Independent link-vertex fan graphs, retaining repeated edges and loops.
    assert all(len(adjacent) == 2 for adjacent in flags.values())
    visited_flags, fans = set(), []
    for flag in flags:
        if flag in visited_flags:
            continue
        stack, component = [flag], set()
        while stack:
            here = stack.pop()
            if here in component:
                continue
            component.add(here)
            stack.extend(flags[here])
        visited_flags.update(component)
        fans.append(component)
    assert len(fans) == 8 and len(vertices.groups()) == 1
    assert sorted(map(len, fans)) == sorted(degrees*2)
    for fan in fans:
        assert len({vertices.find(4*t+i) for t, i, j in fan}) == 1
    V, E, F = len(fans), 6*n, 4*n
    chi = V-E+F
    assert chi < 0 and chi % 2 == 0
    genus = 1-chi//2
    normal_angles = [Fraction(2, degrees[label[o]]) for o in range(6*n)]
    for group in groups:
        assert sum((normal_angles[o] for o in group), Fraction()) == 2
    corner_sums = [sum((normal_angles[6*t+j] for j, edge in enumerate(EDGES)
                       if v in edge), Fraction()) for t in range(n) for v in range(4)]
    maximum = max(corner_sums)
    assert maximum < 1
    expected_maximum = Fraction(13, 33) if special_degree == 6 else Fraction(11, 18)
    assert maximum == expected_maximum
    assert genus == (11 if special_degree == 6 else 5)
    return {'tetrahedra': n, 'degrees': sorted(degrees), 'link': [V, E, F],
            'genus': genus, 'fan_sizes': sorted(map(len, fans)),
            'max_corner_over_pi': str(maximum), 'special_graph_triangle': True,
            'special_graph_loop': True, 'oriented_edge_circles': circles}


def forward_angles(values: list[float]) -> list[float]:
    """The original six-variable length cosine, independent of b_lambda."""
    def value(i: int, j: int) -> float:
        return values[INDEX[tuple(sorted((i, j)))]]
    result = []
    for i, j in EDGES:
        k, l = [v for v in range(4) if v not in (i, j)]
        r, a, b = value(i, j), value(i, k), value(i, l)
        o, c, d = value(k, l), value(j, l), value(j, k)
        rad1 = r*r+a*a+d*d+2*r*a*d-1
        rad2 = r*r+b*b+c*c+2*r*b*c-1
        cosine = (a*b+c*d+r*a*c+r*b*d-(r*r-1)*o)/math.sqrt(rad1*rad2)
        result.append(math.acos(max(-1.0, min(1.0, cosine))))
    return result


def transverse(theta: float, lam: float) -> float:
    if not 0 < theta < PI or not 0 < lam < 1:
        raise ValueError('Require 0<theta<pi and 0<lambda<1')
    return math.atan2(lam*math.cos(theta/2), math.sin(theta/2))


def derivative_data(theta: float, lam: float) -> tuple[float, float]:
    D = math.sin(theta/2)**2+lam*lam*math.cos(theta/2)**2
    return -lam/(2*D), lam*(1-lam*lam)*math.sin(theta)/(4*D*D)


def check_analysis() -> dict[str, object]:
    rng = random.Random(947488)
    counts: Counter[str] = Counter()
    max_formula_error = max_derivative_error = 0.0
    for _ in range(3000):
        h = rng.uniform(1.1, 20)
        Q = rng.uniform(0.3, 20)
        r = 1+2*h*h/Q
        theta_min = 2*math.atan(1/math.sqrt(Q))
        theta = theta_min+(PI-theta_min)*rng.uniform(0.03, 0.97)
        opposite = Q-(Q+1)*math.cos(theta)
        lam = math.sqrt((h*h-1)/(Q+h*h))
        angles = forward_angles([r, h, h, opposite, h, h])
        beta = transverse(theta, lam)
        max_formula_error = max(max_formula_error, abs(theta-angles[0]),
                                *(abs(beta-angles[j]) for j in (1, 2, 4, 5)))
        assert min(angles) > 0
        for v in range(4):
            assert sum(angles[j] for j, edge in enumerate(EDGES) if v in edge) < PI+1e-10
        first, second = derivative_data(theta, lam)
        assert first < 0 < second
        eps = 1e-5
        fd = (transverse(theta+eps, lam)-transverse(theta-eps, lam))/(2*eps)
        max_derivative_error = max(max_derivative_error, abs(fd-first))
        counts['nonsymmetric_opposite_formula_checks'] += 1
        counts['obtuse_target_checks'] += int(theta > PI/2)
    assert max_formula_error < 1e-8 and max_derivative_error < 1e-7
    minimum_surplus = math.inf
    for g in range(3, 41):
        mean = PI/g
        a = PI/(2*g)
        qfloor = 1/math.tan(a)**2
        for _ in range(25):
            Q = qfloor*rng.uniform(1.1, 3)
            h = Q*rng.uniform(1.0, 2)
            r = 1+2*h*h/Q
            lam = math.sqrt((h*h-1)/(Q+h*h))
            theta_min = 2*math.atan(1/math.sqrt(Q))
            noise = [rng.uniform(-1, 1) for _ in range(g)]
            average = sum(noise)/g
            noise = [v-average for v in noise]
            amplitude = 0.7*(mean-theta_min)/max(abs(v) for v in noise)
            targets = [mean+amplitude*v for v in noise]
            assert abs(sum(targets)-PI) < 1e-12
            betas = []
            for theta in targets:
                opposite = Q-(Q+1)*math.cos(theta)
                assert opposite > 1 and r >= 1+2*h-1e-10
                angles = forward_angles([r, h, h, opposite, h, h])
                beta = transverse(theta, lam)
                assert abs(angles[0]-theta) < 1e-7
                assert max(abs(angles[j]-beta) for j in (1, 2, 4, 5)) < 1e-7
                betas.append(beta)
            jensen = g*transverse(mean, lam)
            geometry = g*math.acos(math.tan(a))
            assert sum(betas) >= jensen-1e-10
            assert jensen > geometry > PI/2
            minimum_surplus = min(minimum_surplus, 4*sum(betas)-2*PI)
            counts['shared_parameter_unequal_star_checks'] += 1
            counts['star_genuine_occurrence_checks'] += g
    # Genuine g=2 local family: the g>=3 lemma cannot simply be extended.
    h = Q = 101/100
    r = 1+2*h
    lam = math.sqrt((h*h-1)/(Q+h*h))
    theta = PI/2
    angles = forward_angles([r, h, h, h, h, h])
    assert abs(angles[0]-theta) < 1e-12
    assert abs(lam-1/math.sqrt(101)) < 1e-12
    assert 8*transverse(theta, lam) < 2*PI
    return {**counts, 'max_formula_error': max_formula_error,
            'max_derivative_error': max_derivative_error,
            'minimum_tested_H_angle_surplus': minimum_surplus,
            'g2_local_H_angle_sum': 8*transverse(theta, lam)}


def run() -> dict[str, object]:
    return {'status': 'finite supplementary checks, not formal certification',
            'analytic_seed': 947488,
            'minimum_six_packet': verify_packet(TABLE_SIX, 14, 6),
            'degree_four_packet': verify_packet(TABLE_FOUR, 8, 4),
            'analysis': check_analysis()}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
