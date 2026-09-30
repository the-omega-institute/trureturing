#!/usr/bin/env python3
"""Exact finite supplements for CFMP Sections 133-139.

The general results are written proofs. These tests cover integer identities,
finite kernels, free-word substitutions, and actual cyclic face-pairing links.
No Lean, interval certification, or complete CFMP claim is made.
"""
from __future__ import annotations
import itertools
import json
import math
from collections import defaultdict

Pair = tuple[int, int]
M = ((0, 1), (1, 1))
W = ((1, 1), (1, 0))
D = ((-1, 2), (2, 1))
C = ((2, -1), (1, 2))
S = ((0, 1), (1, 0))
EDGES = ((0, 1), (0, 2), (0, 3), (2, 3), (1, 3), (1, 2))
INDEX = {e: j for j, e in enumerate(EDGES)}


def matmul(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def act(a, z, modulus=None):
    out = tuple(sum(a[i][j]*z[j] for j in range(2)) for i in range(2))
    return out if modulus is None else tuple(v % modulus for v in out)


def mul(x: Pair, y: Pair) -> Pair:
    a, b = x; c, d = y
    return a*c+b*d, a*d+b*c+b*d


def add(x: Pair, y: Pair) -> Pair:
    return x[0]+y[0], x[1]+y[1]


def scale(k: int, x: Pair) -> Pair:
    return k*x[0], k*x[1]


def conjugate(x: Pair) -> Pair:
    return x[0]+x[1], -x[1]


def norm(x: Pair) -> int:
    return x[0]*x[0]+x[0]*x[1]-x[1]*x[1]


def bezout(a: int, b: int) -> tuple[int, int, int]:
    r0, r1, s0, s1, t0, t1 = a, b, 1, 0, 0, 1
    while r1:
        q = r0//r1
        r0, r1 = r1, r0-q*r1
        s0, s1 = s1, s0-q*s1
        t0, t1 = t1, t0-q*t1
    if r0 < 0:
        r0, s0, t0 = -r0, -s0, -t0
    return r0, s0, t0


def check_primitive() -> dict:
    primitive = ramified = decoder_checks = 0
    chosen = []
    delta = (-1, 2)
    assert mul(delta, delta) == (5, 0)
    for c in range(-40, 41):
        for d in range(-40, 41):
            if math.gcd(c, d) != 1:
                continue
            h = c, d; hc = conjugate(h)
            n, tr = norm(h), 2*c+d
            g, r, s = bezout(n, tr)
            assert g in (1, 5)
            assert (g == 5) == (n % 5 == 0)
            assert mul(h, hc) == (n, 0)
            assert tr*tr-4*n == 5*d*d
            primitive += 1
            # Complete R-valued decoder of 1 or of delta.
            first = add(scale(r, hc), (s, 0))
            second = (s, 0)
            assert add(mul(first, h), mul(second, hc)) == (g, 0)
            if g == 5:
                ramified += 1
                assert n % 25 != 0 and d % 5 != 0
                assert (-c+2*d) % 5 == (2*c+d) % 5 == 0
                quotient = ((-c+2*d)//5, (2*c+d)//5)
                assert mul(delta, quotient) == h
                one, a, b = bezout(d, 5)
                assert one == 1
                first = add((a, 0), scale(b, mul(delta, first)))
                second = add((-a, 0), scale(b, mul(delta, second)))
                assert add(mul(first, h), mul(second, hc)) == delta
            decoder_checks += 1
            if len(chosen) < 24 and max(abs(c), abs(d)) <= 4:
                chosen.append(h)
    # Include ramified examples, rational units, and the cited 79 example.
    chosen += [(-1, 2), (2, 1), (7, 1), (8, 5), (1, 0), (0, 1)]
    cases = states = 0
    for h in chosen:
        hc = conjugate(h)
        for m in (2, 3, 5, 10, 15, 25):
            actual = set()
            for z in itertools.product(range(m), repeat=2):
                a, b = mul(h, z), mul(hc, z)
                if all(v % m == 0 for v in a+b):
                    actual.add(z)
                states += 1
            expected = {(0, 0)}
            if norm(h) % 5 == 0 and m % 5 == 0:
                expected = {(2*t*(m//5) % m, t*(m//5) % m) for t in range(5)}
            assert actual == expected
            assert {act(M, z, m) for z in actual} == actual
            cases += 1
    return dict(primitive_pairs=primitive, ramified_pairs=ramified,
                exact_decoder_checks=decoder_checks, modular_kernel_cases=cases,
                enumerated_kernel_states=states)


def check_observation() -> dict:
    assert matmul(D, D) == ((5, 0), (0, 5))
    assert matmul(D, S) == C
    assert matmul(C, W) == matmul(M, C)
    cases = 0
    for m in range(2, 81):
        fibres = defaultdict(list)
        for z in itertools.product(range(m), repeat=2):
            y = act(C, z, m)
            assert act(C, act(W, z, m), m) == act(M, y, m)
            fibres[y].append(z)
        size = math.gcd(5, m)
        assert all(len(fibre) == size for fibre in fibres.values())
        for y, fibre in fibres.items():
            if size == 5:
                assert (2*y[0]+y[1]) % 5 == 0
                phases = {z[0]//(m//5) for z in fibre}
                assert phases == set(range(5))
                if m % 25 == 0:
                    assert len({(z[0] % 5, z[1] % 5) for z in fibre}) == 1
            else:
                assert act(C, fibre[0], m) == y
        cases += 1
    return dict(moduli=cases, highest_digit_phase_checked=True,
                lowest_mod5_readout_failure_checked=True)


def reduce_word(word):
    out = []
    for a in word:
        if out and out[-1] == -a:
            out.pop()
        else:
            out.append(a)
    return tuple(out)


def word_inverse(w):
    return tuple(-a for a in reversed(w))


def substitute(w, images):
    out = []
    for a in w:
        x = images[abs(a)]
        out.extend(x if a > 0 else word_inverse(x))
    return reduce_word(out)


def check_words() -> dict:
    phi = {1: (1, 2), 2: (1,)}
    inv = {1: (2,), 2: (-2, 1)}
    ell, high = (-2, 1, 1), (2, 2, 1)
    boundary = ((-1, -1, 2), (-1, -1, -1, 2, 1), (2, 1, 1, 1))
    count = 0
    for length in range(6):
        for w in itertools.product((1, -1, 2, -2), repeat=length):
            w = reduce_word(w)
            assert substitute(substitute(w, phi), inv) == w
            assert substitute(substitute(w, inv), phi) == w
            chi = lambda z: sum((1 if a > 0 else -1)*(1 if abs(a) == 1 else 2) for a in z) % 5
            assert chi(substitute(w, phi)) == 3*chi(w) % 5
            count += 1
    assert all(sum((1 if a > 0 else -1)*(1 if abs(a) == 1 else 2) for a in w) % 5 == 0
               for w in (ell, high)+boundary)
    assert substitute(ell, phi) == reduce_word((-2,)+high+(2,))
    assert substitute(high, phi) == (1, 1, 1, 2)
    # Exact Fricke-polynomial invariance on a bounded integer grid.
    for x, y, z in itertools.product(range(-7, 8), repeat=3):
        inv0 = x*x+y*y+z*z-x*y*z-2
        xx, yy, zz = z, x, x*z-y
        assert xx*xx+yy*yy+zz*zz-xx*yy*zz-2 == inv0
    return dict(word_tests=count, fricke_grid_tests=15**3)


class DSU:
    def __init__(self, n): self.p = list(range(n))
    def find(self, i):
        while self.p[i] != i:
            self.p[i] = self.p[self.p[i]]; i = self.p[i]
        return i
    def union(self, i, j): self.p[self.find(i)] = self.find(j)
    def groups(self):
        out = defaultdict(list)
        for i in range(len(self.p)): out[self.find(i)].append(i)
        return list(out.values())


def packet(n, u, v):
    p, q = (3, 0, 1, 2), (3, 2, 0, 1)
    return [(i, 0, (i+u) % n, 3, p) for i in range(n)] + [
        (i, 1, (i+v) % n, 2, q) for i in range(n)]


def check_topology(n, u, v):
    faces = {}; edges, verts, dual, ends = DSU(6*n), DSU(4*n), DSU(n), DSU(12*n)
    fans = defaultdict(list)
    for t, f, z, g, p in packet(n, u, v):
        assert p[f] == g and sorted(p) == list(range(4))
        assert sum(p[i] > p[j] for i in range(4) for j in range(i+1, 4)) % 2 == 1
        assert (t, f) not in faces and (z, g) not in faces
        faces[t, f] = z, g, p
        faces[z, g] = t, f, tuple(p.index(i) for i in range(4))
        dual.union(t, z)
        for a in range(4):
            if a != f: verts.union(4*t+a, 4*z+p[a])
        for j, (a, b) in enumerate(EDGES):
            if f in (a, b): continue
            jj = INDEX[tuple(sorted((p[a], p[b])))]; x, y = 6*t+j, 6*z+jj
            edges.union(x, y)
            for end in (0, 1):
                xx, yy = 2*x+end, 2*y+(end ^ (p[a] > p[b]))
                ends.union(xx, yy); fans[xx].append(yy); fans[yy].append(xx)
    assert len(faces) == 4*n and len(dual.groups()) == len(verts.groups()) == 1
    groups = edges.groups()
    assert sorted(map(len, groups)) == [3*n, 3*n]
    assert len(ends.groups()) == 4
    for j in range(6*n): assert ends.find(2*j) != ends.find(2*j+1)
    for group in groups:
        t, j = divmod(group[0], 6); a, b = EDGES[j]
        entry = min(x for x in range(4) if x not in (a, b)); initial = (t, a, b, entry)
        state = initial; visited = []
        for step in range(len(group)):
            tt, aa, bb, incoming = state
            visited.append(6*tt+INDEX[tuple(sorted((aa, bb)))])
            outgoing = next(x for x in range(4) if x not in (aa, bb, incoming))
            zz, gg, pp = faces[tt, outgoing]
            state = zz, pp[aa], pp[bb], gg
            assert state != initial or step == len(group)-1
        assert state == initial and sorted(visited) == sorted(group)
    for group in ends.groups():
        assert all(len(fans[j]) == 2 for j in group)
        visited = set(); todo = [group[0]]
        while todo:
            j = todo.pop()
            if j in visited: continue
            visited.add(j); todo.extend(fans[j])
        assert visited == set(group)
    assert 4-6*n+4*n == 2-2*(n-1)
    return dict(tetrahedra=n, edge_degrees=[3*n, 3*n], link=[4, 6*n, 4*n], genus=n-1)


def check_cover_families() -> dict:
    summaries = []; phase_tests = evolution_tests = 0
    for k in (1, 2, 3):
        n = 5**k; base_output = (-1 % n, 2 % n)
        states = [(j*(n//5), (1+2*j*(n//5)) % n) for j in range(5)]
        for j, uv in enumerate(states):
            assert act(C, uv, n) == base_output
            data = check_topology(n, *uv)
            if j == 0: summaries.append(data)
            phase_tests += 1
        for _ in range(16):
            assert len(set(states)) == 5
            assert {act(C, z, n) for z in states} == {base_output}
            assert all(math.gcd(x, n) == 1 for x in base_output)
            # An isomorphism over the fixed base commutes with a unit return,
            # hence is a translation. No translation changes the input pair.
            assert len({z for z in states}) == 5
            states = [act(W, z, n) for z in states]
            base_output = act(M, base_output, n)
            evolution_tests += 5
        theta = 2*math.pi/(3*n); cc = math.cos(theta); xx = cc/(2*cc-1)
        assert xx > 1 and abs(xx/(2*xx-1)-cc) < 1e-14
    return dict(families=summaries, actual_packet_checks=phase_tests,
                fibonacci_phase_evolution_checks=evolution_tests,
                distinctness='marked covers over the fixed framed base only')


def main():
    if not __debug__: raise RuntimeError('Run without -O.')
    print(json.dumps(dict(primitive=check_primitive(), observation=check_observation(),
                         words=check_words(), covers=check_cover_families(),
                         status='Exact finite supplements; written general proofs, no new formal certification.'),
                     indent=2, sort_keys=True))

if __name__ == '__main__': main()
