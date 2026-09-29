#!/usr/bin/env python3
"""Exact original-owner line defects and actual covering controls; no Lean claims."""
from collections import Counter, defaultdict
from fractions import Fraction as F
from itertools import combinations
from math import lcm, prod
from pathlib import Path
import argparse
import json

def need(ok, message):
    if not ok:
        raise ValueError(message)

def factor(n):
    out = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = 1
    return out

def c2(n):
    return n * (n - 1) // 2

def analyze(name, classes, local_lower=None):
    L = lcm(*(m for m, a in classes))
    heights = factor(L)
    R = prod(heights)
    N = L // R
    support = []
    phase = []
    for m, a in classes:
        fm = factor(m)
        A = tuple(p for p, H in heights.items() if fm.get(p, 0) == H)
        support.append(A)
        phase.append({p: (a % (p ** heights[p])) // p ** (heights[p] - 1) for p in A})
    owner = [-1] * L
    multiplicity = [0] * L
    for s in sorted(range(len(classes)), key=lambda s: (classes[s][0], s)):
        m, a = classes[s]
        for x in range(a % m, L, m):
            multiplicity[x] += 1
            if owner[x] == -1:
                owner[x] = s
    owned = [set() for _ in classes]
    private = [set() for _ in classes]
    for x, s in enumerate(owner):
        if s != -1:
            owned[s].add(x)
            if multiplicity[x] == 1:
                private[s].add(x)
    need(all(private), 'each literal original class has a private witness')
    Z = [{x % N for x in O} for O in owned]
    by_support = defaultdict(list)
    for s, A in enumerate(support):
        by_support[A].append(s)
    Fs = {}
    for s, A in enumerate(support):
        for p in A:
            Fs[s, p] = {(y + j * (L // p)) % L for y in owned[s] for j in range(1, p)}
            need(len(Fs[s, p]) == (p - 1) * len(owned[s]), 'literal p-top owner preimage count')

    def check(W, tag):
        XW = {x for x in range(L) if x % N in W}
        B = {}
        defect = {}
        omega = {}
        caps = {}
        shadow = {}
        checks = 0
        for A, ss in by_support.items():
            YA = set().union(*(owned[s] for s in ss)) & XW
            omega[A] = F(len(YA), L)
            for z in W:
                active = [s for s in ss if z in Z[s]]
                keys = [tuple(phase[s][q] for q in A) for s in active]
                need(len(keys) == len(set(keys)), 'one owned support/phase at each actual lower source')
            for p in A:
                lines = Counter(x % (L // p) for x in YA)
                literal = sum(len(Fs[s, p] & Fs[t, p] & XW) for s, t in combinations(ss, 2))
                b = F(literal, L)
                delta = F((p - 2) * sum(h * (p - h) for h in lines.values()), 2 * L)
                need(b == F((p - 2) * sum(c2(h) for h in lines.values()), L), 'exact original-owner line count')
                need(b + delta == c2(p - 1) * omega[A], 'exact line defect')
                cap = F(p - 2, 2) * (min(p, len(ss)) - 1) * omega[A]
                need(b <= cap, 'arithmetic inventory cap')
                fibre_cap = F(0)
                for z in W:
                    n = sum(x % N == z for x in YA)
                    K = sum(z in Z[s] for s in ss)
                    fibre_cap += F((p - 2) * n * max(K - 1, 0), 2 * L)
                need(b <= fibre_cap, 'owner-positive fibre cap')
                adj = [(s, t) for s, t in combinations(ss, 2)
                       if [q for q in A if phase[s][q] != phase[t][q]] == [p]]
                cs = sum((F(len(W & Z[s] & Z[t]), N) for s, t in adj), F(0))
                if p > 2:
                    need(cs + F(R, p - 2) * b <= R * (p - 1) * omega[A], 'joint shadow/shell tradeoff')
                B[A, p] = b
                defect[A, p] = delta
                caps[A, p] = cap
                shadow[A, p] = cs
                checks += 6
        for p in heights:
            As = [A for A in by_support if p in A]
            miss = F(0)
            mix = F(0)
            for x in XW:
                ks = [sum(x in Fs[s, p] for s in by_support[A]) for A in As]
                k = sum(ks)
                need(k <= p - 1, 'one owner per alternative top phase')
                miss += F(k * (p - 1 - k), 2 * L)
                mix += F(sum(a * b for a, b in combinations(ks, 2)), L)
            need(sum((defect[A, p] for A in As), F(0)) == miss + mix, 'two-defect identity')
            checks += 1
        for A, ss in by_support.items():
            if any(p == 2 for p in A):
                continue
            cs = F(0)
            mixed = F(0)
            for s, t in combinations(ss, 2):
                diff = [p for p in A if phase[s][p] != phase[t][p]]
                if 1 <= len(diff) <= 2:
                    cs += F(len(W & Z[s] & Z[t]), N)
                if len(diff) == 2:
                    p, q = diff
                    mixed += F(len(Fs[s, p] & Fs[t, q] & XW) + len(Fs[s, q] & Fs[t, p] & XW), L)
            d = sum(p - 1 for p in A) + sum((p - 1) * (q - 1) for p, q in combinations(A, 2))
            lhs = cs + sum((F(R, p - 2) * B[A, p] for p in A), F(0)) + F(R, 2) * mixed
            need(lhs <= R * d * omega[A], 'combined distance-one/two tradeoff')
            checks += 1
        rows = []
        for p in heights:
            As = [A for A in by_support if p in A]
            rows.append(dict(p=p, owner_mass=str(sum((omega[A] for A in As), F(0))),
                pair_capacity=str(sum((B[A, p] for A in As), F(0))),
                exact_defect=str(sum((defect[A, p] for A in As), F(0))),
                inventory_cap=str(sum((caps[A, p] for A in As), F(0)))))
        return dict(tag=tag, lower_count=len(W), lower_mass=str(F(len(W), N)), checks=checks, prime_rows=rows), (XW, B, defect, omega, caps)

    global_result, _ = check(set(range(N)), 'all original lower sources')
    local_result = None
    if local_lower is not None:
        local_result, data = check(set(local_lower), 'specified whole top fibres only')
        XW, B, defect, omega, caps = data
        need(all(multiplicity[x] == 1 for x in XW), 'complete private tiling on the specified actual top fibres')
        demand = 0
        for x in XW:
            p = 5
            counts = Counter()
            for j in range(1, p):
                y = (x + j * (L // p)) % L
                need(multiplicity[y] == 1, 'unique actual supplier for every alternative phase')
                counts[support[owner[y]]] += 1
            demand += sum(c2(k) for k in counts.values())
        phi = F(demand, L)
        total_b = sum((v for (A, p), v in B.items() if p == 5), F(0))
        total_delta = sum((v for (A, p), v in defect.items() if p == 5), F(0))
        total_cap = sum((v for (A, p), v in caps.items() if p == 5), F(0))
        mass = F(len(XW), L)
        need(phi == total_b and phi + total_delta == 6 * mass, 'positive exact defect coexists with equality in demand/capacity')
        need(phi / mass == F(18, 5) and total_delta / mass == F(12, 5), 'exact conditional values')
        need(total_cap / mass == F(21, 5), 'inventory cap improves six without forcing contradiction')
        collision_supports = []
        g = 0
        for A, ss in by_support.items():
            K = sum(0 in Z[s] for s in ss)
            if K >= 2:
                need(5 in A and K < 5, 'every collision support meets demanded prime and has K<p')
                collision_supports.append(dict(support=A, K=K))
                g = max(g, K * 3 * (5 - K))
        need(g == 18, 'positive source-local collision-defect term')
        need(len({m for m, a in classes}) == len(classes) and all(m > 1 and m % 2 for m, a in classes), 'odd distinct literal moduli')
        for A, ss in by_support.items():
            need(len(ss) <= prod(H for p, H in heights.items() if p not in A), 'same original numerical-inventory bound')
        local_result.update(phi_integral=str(phi), phi_given_source=str(phi / mass),
            defect_given_source=str(total_delta / mass), inventory_cap_given_source=str(total_cap / mass),
            old_cap_given_source='6', collision_supports=collision_supports,
            g=g, g_term_given_source=str(F(g, 2 * R)),
            scope='Actual odd-distinct irredundant NONCOVER; complete top coverage is asserted only over lower source zero.')
    return dict(name=name, classes=[dict(modulus=m,residue=a) for m,a in classes], period=L,
        global_heights=heights, lower_modulus=N, top_size=R,
        uncovered_count=sum(c == 0 for c in multiplicity), private_witnesses=[min(P) for P in private],
        global_check=global_result, local_check=local_result)

cases = [
    analyze('odd_distinct_local_whole_fibre', [(5,1),(35,7),(245,98),(1715,1029),(15,0),(105,70),(735,245),(2401,1)], [0]),
    analyze('distinct_even_whole_control', [(2,1),(4,2),(3,1),(6,2),(5,1),(10,2),(20,8),(15,0),(30,24)]),
    analyze('repeated_odd_whole_control', [(15,a) for a in range(15)]),
]
need(cases[0]['uncovered_count'] > 0, 'local construction remains explicitly a noncover')
need(all(case['uncovered_count'] == 0 for case in cases[1:]), 'whole-cover control scope')
out = dict(scope='Exact finite original-AP/owner controls. No Lean verification or unrestricted covering theorem.', cases=cases)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, default=Path(__file__).with_suffix('.json'))
options = parser.parse_args()
options.output.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
