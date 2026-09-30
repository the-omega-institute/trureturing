#!/usr/bin/env python3
"""Supplementary checks for CFMP continuation Sections 81-87.

Standard-library only. Finite tests do not prove the continuous estimates,
realize random count vectors as triangulations, or certify the CFMP conjecture.
Local edge order: (01,02,03,23,13,12).
"""
from __future__ import annotations

import json
import math
import random
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product

EDGES = ((0, 1), (0, 2), (0, 3), (2, 3), (1, 3), (1, 2))
INDEX = {edge: i for i, edge in enumerate(EDGES)}
PI = math.pi


def at(values: list[float], i: int, j: int) -> float:
    return values[INDEX[tuple(sorted((i, j)))]]


def corners(angles: list[float]) -> list[float]:
    return [sum(at(angles, i, j) for j in range(4) if j != i)
            for i in range(4)]


def length_cosines(angles: list[float]) -> list[float]:
    """Frigerio-Moraschini (1),(3),(4), with vertex determinants."""
    if min(angles) <= 0 or max(corners(angles)) >= PI:
        raise ValueError("Angles must lie in the genuine hyperideal angle domain")
    out = []
    for i, j in EDGES:
        k, h = [v for v in range(4) if v not in (i, j)]
        theta = at(angles, i, j)
        a, b = at(angles, i, k), at(angles, i, h)
        c, d = at(angles, j, h), at(angles, j, k)
        g = at(angles, k, h)
        z = math.cos(theta)
        D1 = (z + math.cos(a + b)) * (z + math.cos(a - b))
        D2 = (z + math.cos(c + d)) * (z + math.cos(c - d))
        numerator = (math.sin(theta)**2 * math.cos(g)
                     + math.cos(a)*math.cos(d) + math.cos(b)*math.cos(c)
                     + z*(math.cos(a)*math.cos(c) + math.cos(b)*math.cos(d)))
        x = numerator / math.sqrt(D1 * D2)
        assert x > 1.0 - 1e-10
        out.append(x)
    return out


def forward_angles(x: list[float]) -> list[float]:
    """Independent forward formula, with face length determinants."""
    out = []
    for i, j in EDGES:
        k, h = [v for v in range(4) if v not in (i, j)]
        r, a, b = at(x, i, j), at(x, i, k), at(x, i, h)
        o, c, d = at(x, k, h), at(x, j, h), at(x, j, k)
        A = r*r + a*a + d*d + 2*r*a*d - 1
        B = r*r + b*b + c*c + 2*r*b*c - 1
        value = (a*b + c*d + r*a*c + r*b*d - (r*r-1)*o) / math.sqrt(A*B)
        out.append(math.acos(max(-1.0, min(1.0, value))))
    return out


def U(theta: float, sigma: float) -> float:
    if not 0 < theta < sigma < PI:
        raise ValueError("Require 0 < theta < sigma < pi")
    return math.sin(theta) / (math.cos(theta) + math.cos(sigma-theta))


def phi(theta: float, bound: float) -> float:
    if not 0 < theta <= PI/4 or bound < 3:
        raise ValueError("Require 0 < theta <= pi/4 and bound >= 3")
    q = math.sqrt((bound-1)/2)
    return theta + math.acos(math.sin(theta)/q - math.cos(theta))


# A complete fixed packet; no randomized search is needed to reproduce it.
PACKET_ROWS = """
0 2 1 3 0132
1 2 2 2 1023
2 3 3 2 0132
3 3 4 3 1023
4 2 5 2 1023
5 3 0 3 1023
9 2 5 1 0213
7 0 8 1 1230
6 3 4 0 3120
5 0 9 3 3012
9 1 10 0 1023
3 0 10 3 3120
6 2 2 0 1302
10 1 1 0 3012
6 0 7 3 3012
8 0 0 0 0213
7 1 4 1 0132
3 1 10 2 1230
2 1 8 3 1302
7 2 1 1 2310
8 2 9 0 2103
0 1 6 1 2103
"""


class DSU:
    def __init__(self, n: int) -> None:
        self.parent = list(range(n))

    def find(self, x: int) -> int:
        while self.parent[x] != x:
            self.parent[x] = self.parent[self.parent[x]]
            x = self.parent[x]
        return x

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a != b:
            self.parent[a] = b

    def groups(self) -> list[list[int]]:
        out: dict[int, list[int]] = {}
        for x in range(len(self.parent)):
            out.setdefault(self.find(x), []).append(x)
        return list(out.values())


def check_packet() -> dict[str, object]:
    """Exact incidence, oriented-return, link-fan and rational-angle checks."""
    rows = []
    for line in PACKET_ROWS.strip().splitlines():
        t, f, u, g, p = line.split()
        rows.append((int(t), int(f), int(u), int(g), tuple(map(int, p))))
    faces = {}
    vertices, edges, blocks = DSU(44), DSU(66), DSU(11)
    flag_adj = {(t, i, j): [] for t in range(11)
                for i in range(4) for j in range(4) if i != j}
    for t, f, u, g, p in rows:
        assert p[f] == g and sorted(p) == list(range(4))
        assert sum(p[i] > p[j] for i in range(4)
                   for j in range(i+1, 4)) % 2 == 1
        assert (t, f) != (u, g)
        assert (t, f) not in faces and (u, g) not in faces
        inv = tuple(p.index(i) for i in range(4))
        faces[t, f] = (u, g, p)
        faces[u, g] = (t, f, inv)
        blocks.union(t, u)
        for i in range(4):
            if i != f:
                vertices.union(4*t+i, 4*u+p[i])
            for j in range(4):
                if i != j and i != f and j != f:
                    a, b = (t, i, j), (u, p[i], p[j])
                    flag_adj[a].append(b)
                    flag_adj[b].append(a)
                    edges.union(6*t+INDEX[tuple(sorted((i, j)))],
                                6*u+INDEX[tuple(sorted((p[i], p[j])))])
    assert len(faces) == 44 and len(blocks.groups()) == 1
    cls = edges.groups()
    assert len(cls) == 3 and len(vertices.groups()) == 1
    Uc = next(c for c in cls if 0 in c)
    Vc = next(c for c in cls if 3 in c)
    Hc = next(c for c in cls if c is not Uc and c is not Vc)
    assert Uc == [0, 6, 12, 18, 24, 30]
    assert Vc == [3, 13, 17, 20, 22, 33, 38, 48, 52, 58, 59, 60]
    labels = {x: label for c, label in [(Uc, 'U'), (Vc, 'V'), (Hc, 'H')] for x in c}
    deg = {'U': len(Uc), 'V': len(Vc), 'H': len(Hc)}
    assert deg == {'U': 6, 'V': 12, 'H': 48}
    local = [[labels[6*t+j] for j in range(6)] for t in range(11)]
    assert all(row.count('U') <= 1 and row.count('V') <= 2
               and row.count('H') >= 3 for row in local)
    assert sum(row.count('V') == 2 for row in local) == 4
    # One complete normal circle per actual global edge, with ordered endpoints.
    circles = []
    for group in (Uc, Vc, Hc):
        t, j = divmod(min(group), 6)
        i, k = EDGES[j]
        f = min(v for v in range(4) if v not in (i, k))
        initial = (t, i, k, f)
        state = initial
        seen = []
        for step in range(len(group)):
            tt, a, b, entry = state
            seen.append(6*tt+INDEX[tuple(sorted((a, b)))])
            exitface = next(v for v in range(4) if v not in (a, b, entry))
            uu, gg, pp = faces[tt, exitface]
            state = (uu, pp[a], pp[b], gg)
            assert state != initial or step == len(group)-1
        assert state == initial and sorted(seen) == group
        circles.append(seen)
    # Independent link-vertex graph check, including both ends of loops.
    assert all(len(adj) == 2 for adj in flag_adj.values())
    used, fan_sizes = set(), []
    for flag in flag_adj:
        if flag in used:
            continue
        stack, component = [flag], set()
        while stack:
            here = stack.pop()
            if here in component:
                continue
            component.add(here)
            stack.extend(flag_adj[here])
        used.update(component)
        fan_sizes.append(len(component))
    assert sorted(fan_sizes) == [6, 6, 12, 12, 48, 48]
    link_V, link_E, link_F = len(fan_sizes), 3*len(rows), 44
    assert (link_V, link_E, link_F) == (6, 66, 44)
    assert 3*link_F == 2*link_E
    chi = link_V-link_E+link_F
    assert chi == -16 and 1-chi//2 == 9
    norm_angles = [Fraction(2, deg[labels[o]]) for o in range(66)]
    for group in (Uc, Vc, Hc):
        assert sum((norm_angles[o] for o in group), Fraction()) == 2
    corner_sums = [sum((norm_angles[6*t+j] for j, edge in enumerate(EDGES)
                       if v in edge), Fraction()) for t in range(11) for v in range(4)]
    assert max(corner_sums) == Fraction(13, 24) < 1
    types = Counter()
    for row in local:
        canonical = min(tuple(row[INDEX[tuple(sorted((p[i], p[j])))]]
                              for i, j in EDGES) for p in permutations(range(4)))
        types[canonical] += 1
    assert len(types) == 6 and types[('H',)*6] == 1
    # Exhaustive flat-state checks after the proved f<=2 reduction.
    opposite_pairs = ((0, 3), (1, 4), (2, 5))
    candidate_count = capacity_eliminations = saturated_eliminations = 0
    for fcount in (1, 2):
        for chosen in combinations(range(11), fcount):
            for selected_pairs in product(range(3), repeat=fcount):
                candidate_count += 1
                flat = set(chosen)
                n, m = Counter(), Counter()
                for t, pair in zip(chosen, selected_pairs):
                    n.update(local[t])
                    m.update(local[t][j] for j in opposite_pairs[pair])
                if any(m[L] > 2 or (m[L] == 2 and n[L] != deg[L]) for L in deg):
                    saturated_eliminations += 1
                    continue
                assert fcount == 1 and sum(m.values()) == 2
                pi_labels = [L for L in deg if m[L] == 1]
                assert len(pi_labels) == 2
                for e in pi_labels:
                    if e == 'H':
                        continue
                    mu = {L: 0 for L in deg}
                    for t in range(11):
                        if t in flat:
                            continue
                        for j, f_label in enumerate(local[t]):
                            value = sum(k != j and local[t][k] == e
                                        and bool(set(EDGES[k]) & set(EDGES[j]))
                                        for k in range(6))
                            mu[f_label] = max(mu[f_label], value)
                    cap = 2*(2-m[e])+sum(mu[L]*(2-m[L]) for L in deg)
                    assert deg[e]-n[e] >= cap  # forces x_e<3 by the written theorem
                assert set(pi_labels) == {'U', 'V'} or n['H'] >= 3
                capacity_eliminations += 1
    assert candidate_count == 528
    assert candidate_count == saturated_eliminations+capacity_eliminations
    return {'packet_degrees': deg, 'packet_link': [link_V, link_E, link_F],
            'packet_genus': 9, 'packet_fan_sizes': sorted(fan_sizes),
            'packet_max_corner_over_pi': str(max(corner_sums)),
            'packet_local_type_count': len(types),
            'packet_flat_state_checks': candidate_count,
            'packet_saturation_eliminations': saturated_eliminations,
            'packet_capacity_eliminations': capacity_eliminations}


def angular_weight(bound: float) -> float:
    if bound < 3:
        raise ValueError('The weighted angular demand requires bound >= 3')
    return PI/math.acos((3-bound)/(bound+1))


def run() -> dict[str, object]:
    rng = random.Random(947475)
    counts: Counter[str] = Counter()
    max_roundtrip = 0.0
    for _ in range(4000):
        # Nonsymmetric inputs, including obtuse target angles and caps > pi/2.
        raw = [math.exp(rng.uniform(-2.5, 2.5)) for _ in EDGES]
        factor = PI*rng.uniform(0.12, 0.985)/max(corners(raw))
        angles = [a*factor for a in raw]
        sums = corners(angles)
        x = length_cosines(angles)
        recovered = forward_angles(x)
        max_roundtrip = max(max_roundtrip,
                            max(abs(a-b) for a, b in zip(angles, recovered)))
        for edge_index, (i, j) in enumerate(EDGES):
            theta = angles[edge_index]
            s1, s2 = sums[i], sums[j]
            fine = math.asinh(U(theta, s1)) + math.asinh(U(theta, s2))
            coarse = math.asinh(math.tan(s1/2)) + math.asinh(math.tan(s2/2))
            ell = math.acosh(max(1.0, x[edge_index]))
            assert ell < fine + 1e-10 and fine < coarse + 1e-10
            coupled = 1+2*math.sin(theta)**2/((math.cos(theta)+math.cos(s1-theta))
                                               *(math.cos(theta)+math.cos(s2-theta)))
            assert x[edge_index] < coupled+1e-10
            if x[edge_index] >= 3:
                demand = angular_weight(x[edge_index])*theta+s1+s2-2*theta
                assert demand > PI-1e-10
                counts['length_weighted_demand_checks'] += 1
            counts['full_range_edge_checks'] += 1
            counts['obtuse_target_checks'] += int(theta > PI/2)
            counts['large_endpoint_cap_checks'] += int(max(s1, s2) > PI/2)
            if theta <= PI/4 and x[edge_index] > 3:
                assert max(s1, s2) > phi(theta, 3) - 1e-10
                assert max(s1, s2) > 3*PI/4
                counts['large_corner_witness_checks'] += 1
    assert max_roundtrip < 1e-7
    assert counts['obtuse_target_checks'] > 0
    assert counts['large_corner_witness_checks'] > 0

    # Sharp equal-cap family throughout (0,pi), including the new obtuse range.
    for sigma in (PI/3, 2*PI/3, 5*PI/6):
        limit = (3-math.cos(sigma))/(1+math.cos(sigma))
        errors = []
        for eps in (1e-3, 1e-4, 1e-5, 1e-6):
            x = length_cosines([sigma-2*eps, eps, eps, eps, eps, eps])[0]
            assert x < limit
            errors.append(limit-x)
        assert all(b < a for a, b in zip(errors, errors[1:]))
        assert errors[-1] < 1e-3
        counts['sharp_family_sequences'] += 1

    # Integer occurrence identities and exact strict-remainder support.
    # These vectors are NOT claimed to come from face-paired manifolds.
    for f in range(1, 51):
        for _ in range(20):
            saturated = rng.randrange(f+1)
            single = 2*f-2*saturated
            zero = rng.randrange(1, 2*f+2)
            m = [2]*saturated + [1]*single + [0]*zero
            n = [6]*saturated + [1]*single + [0]*zero
            for _ in range(6*f-sum(n)):
                n[rng.randrange(len(n))] += 1
            assert sum(m) == 2*f and sum(n) == 6*f
            exposed = [i for i in range(len(m)) if m[i] == 1 and n[i] in (1, 2)]
            rest = [i for i in range(len(m)) if i not in exposed]
            assert len(exposed) <= 2*f
            assert any(n[i] > 0 for i in rest)
            x = [rng.uniform(1.01, 20) for _ in m]
            h = [math.log(t/(t-1)) for t in x]
            G = sum((3*mi-ni)*math.log(t)-2*mi*hi
                    for mi, ni, t, hi in zip(m, n, x, h))
            shifted = sum(2*math.log(x[i]-1)-(n[i]-1)*math.log(x[i])
                          for i in exposed)
            remainder = sum((n[i]-3*m[i])*math.log(x[i])+2*m[i]*h[i]
                            for i in rest)
            assert remainder > 0
            assert abs(shifted-G-remainder) < 1e-9
            counts['occurrence_identity_checks'] += 1

    # Threshold monotonicity and complementary-cap tangent criterion.
    for bound in (3., 5., 10., 100.):
        vals = [phi(PI/(g+2), bound) for g in range(2, 101)]
        assert all(3*PI/4-1e-12 <= v < PI for v in vals)
        assert all(a < b for a, b in zip(vals, vals[1:]))
        counts['threshold_monotonicity_sequences'] += 1
    for j in range(1, 1000):
        sigma = PI*j/1000
        assert abs(math.tan(sigma/2)*math.tan((PI-sigma)/2)-1) < 1e-10
        counts['complementary_cap_checks'] += 1

    # Explicit local six-star survives: not a complete CFMP counterexample.
    r, t = 4., 5.
    opposite = (147-53*math.sqrt(5))/12
    theta = PI/5
    genuine = forward_angles([r,t,t,opposite,t,t])
    flat = forward_angles([r,t,t,103/3,t,t])
    assert abs(flat[0]-PI) < 1e-7 and abs(flat[3]-PI) < 1e-7
    assert all(abs(flat[k]) < 1e-7 for k in (1,2,4,5))
    assert abs(genuine[0]-theta) < 1e-12
    assert abs(flat[0]+5*genuine[0]-2*PI) < 1e-7
    assert max(corners(genuine)) < PI
    assert corners(genuine)[0] > phi(theta, 3)
    return {'seed': 947475, **dict(counts), **check_packet(),
            'max_angle_roundtrip_error': max_roundtrip,
            'five_genuine_occurrence_threshold_degrees': phi(PI/5, 3)*180/PI,
            'local_star_corner_degrees': corners(genuine)[0]*180/PI,
            'status': 'supplementary finite checks only; no Lean or full CFMP certification'}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
