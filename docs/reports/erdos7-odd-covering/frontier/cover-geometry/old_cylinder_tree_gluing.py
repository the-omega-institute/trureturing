#!/usr/bin/env python3
"""Exact original-cut and old-cylinder tree-gluing diagnostics.

Finite valuation cells retain every old state with its Haar mass. No random
sampling, floating logarithms, or independent resampling of old boundaries.
"""
import argparse
from fractions import Fraction as F
from itertools import product
from math import gcd, lcm


def require(test, message):
    if not test:
        raise ValueError(message)


def tree_mass(marginals, pairs, center):
    others = [i for i in range(3) if i != center]
    return pairs[tuple(sorted((center, others[0])))] * pairs[
        tuple(sorted((center, others[1])))] / marginals[center]


def valuation(n, q):
    out = 0
    while n % q == 0:
        n //= q
        out += 1
    return out


def forest_gap(ds, center, q):
    aa = [valuation(d, q) for d in ds]
    edges = [(center, i) for i in range(3) if i != center]
    gap = sum(aa) - sum(min(aa[i], aa[j]) for i, j in edges) - max(aa)
    by_levels = 0
    for height in range(1, max(aa) + 1):
        active = {i for i, a in enumerate(aa) if a >= height}
        edge_count = sum(i in active and j in active for i, j in edges)
        by_levels += len(active) - edge_count - 1
    require(gap == by_levels and gap >= 0, 'Exact threshold forest gap')
    return gap


def original_cut(height):
    require(height >= 2, 'Eight fixed cofactors divide 105^H only for H>=2')
    p = 11
    ds = [15**height, 21**height, 35**height, 3, 5, 7, 9, 15, 21, 25, 35]
    old_period = 105**height
    require(len(set(ds)) == p and lcm(*ds) == old_period,
            'Distinct literal old cofactors and complete old period')
    rows = []
    for root, d in enumerate(ds):
        a = d * ((root * pow(d, -1, p)) % p)
        private = old_period * ((root * pow(old_period, -1, p)) % p)
        rows.append((a, p*d, private))
    require(len({d for _, d, _ in rows}) == p, 'Original (d,e) uniqueness')
    require(all(d > 1 and d % 2 for _, d, _ in rows), 'Odd original moduli')
    for i, (_, _, private) in enumerate(rows):
        for j, (a, d, _) in enumerate(rows):
            require((private % d == a) == (i == j), 'Actual private integer')

    total = F(0)
    selected_joint = F(0)
    cells = 0
    partitions = []
    for q in (3,5,7):
        levels = sorted({0,height} | {valuation(d,q) for d in ds})
        atoms = [(a,F(1,q**a)-F(1,q**b)) for a,b in zip(levels,levels[1:])]
        atoms.append((height,F(1,q**height)))
        require(sum(weight for _,weight in atoms)==1, 'Complete old valuation partition')
        partitions.append(atoms)
    for atom_tuple in product(*partitions):
        exponents = [a for a,_ in atom_tuple]
        representative = 1
        mass = F(1)
        for q, (e,weight) in zip((3,5,7),atom_tuple):
            representative *= q**e
            mass *= weight
        active = [representative % d == 0 for d in ds]
        # Exactly one possible original label per current root, so W is 0 or 1.
        W = int(all(active))
        require(W == int(all(e == height for e in exponents)),
                'Unique cut exactly on old0, explicit failure everywhere else')
        ts = [W] * p
        require(sum(F(t, p) for t in ts) == W, 'Normalized cut Kraft identity')
        # One actual integer for each root checks the complete fibre pullback.
        for root in range(p):
            actual = representative + old_period * (
                ((root-representative) * pow(old_period, -1, p)) % p)
            require([actual % d == a for a, d, _ in rows] ==
                    [is_active and label == root for label, is_active in enumerate(active)],
                    'Literal original memberships on every old valuation cell and current root')
        selected_joint += mass * ts[0] * ts[1] * ts[2]
        total += mass
        cells += 1
    require(total == 1 and selected_joint == F(1, old_period),
            'All-old source retained and exact nonlinear selection moment')

    first = ds[:3]
    marginals = [F(1, d) for d in first]
    pairs = {(i,j): F(1, lcm(first[i], first[j]))
             for i in range(3) for j in range(i+1,3)}
    trees = [tree_mass(marginals, pairs, center) for center in range(3)]
    ratios = [selected_joint / x for x in trees]
    require(ratios == [7**height, 5**height, 3**height], 'All three tree corrections')
    for center in range(3):
        correction = 1
        for q in (3,5,7):
            correction *= q**forest_gap(first, center, q)
        require(correction == ratios[center], 'Forest correction equals exact probability ratio')
    return dict(height=height, labels=p, old_period=old_period, old_cells=cells,
                private_checks=p*p, fibre_memberships=cells*p*p,
                selected_joint=str(selected_joint), best_tree=str(max(trees)),
                best_tree_correction=3**height)


def boundary_bit_law():
    states = list(product((0,1), repeat=3))
    actual = {state:F(0) for state in states}
    for x in range(15):
        actual[(int(x%3==0), int(x%15==0), int(x%5==0))] += F(1,15)
    left = {(a,b):sum(v for (x,y,z),v in actual.items() if (x,y)==(a,b))
            for a,b in product((0,1),repeat=2)}
    right = {(b,c):sum(v for (x,y,z),v in actual.items() if (y,z)==(b,c))
             for b,c in product((0,1),repeat=2)}
    middle = {b:sum(v for (x,y,z),v in actual.items() if y==b) for b in (0,1)}
    glued = {(a,b,c):left[(a,b)]*right[(b,c)]/middle[b] for a,b,c in states}
    require(sum(glued.values()) == 1, 'Tree join is a normalized probability')
    for a,b in product((0,1),repeat=2):
        require(sum(v for (x,y,z),v in glued.items() if (x,y)==(a,b)) == left[(a,b)],
                'Tree join preserves left pair marginal')
    for b,c in product((0,1),repeat=2):
        require(sum(v for (x,y,z),v in glued.items() if (y,z)==(b,c)) == right[(b,c)],
                'Tree join preserves right pair marginal')
    require(actual[(1,1,1)] == glued[(1,1,1)] == F(1,15), 'All-ones mass equality')
    require(actual[(1,0,1)] == 0 and glued[(1,0,1)] == F(4,105),
            'Preserved pair marginals still invent an impossible joint event')
    return dict(actual_forbidden=str(actual[(1,0,1)]), glued_forbidden=str(glued[(1,0,1)]),
                shared_all_ones=str(actual[(1,1,1)]))


def survivor_restriction():
    rows = ((0,105), (12,33), (35,55), (14,77))
    private_points = (0,12,35,14)
    require(len({d for _,d in rows}) == len(rows) and
            all(d > 1 and d % 2 for _,d in rows),
            'Distinct odd original moduli in the survivor example')
    for i, point in enumerate(private_points):
        require([point % d == a for a,d in rows] ==
                [i == j for j in range(len(rows))],
                'Each survivor-example original label has its own private point')
    period = lcm(*(d for _,d in rows))
    for point in range(period):
        actual = [point % d == a for a,d in rows]
        expected = [point % 105 == 0] + [
            point % q == 0 and point % 11 == root
            for q,root in ((3,1),(5,2),(7,3))]
        require(actual == expected, 'Survivor and current-root source pullback')
    carrier = range(1,105)  # The original old label 0 mod105 is excluded.
    ds = (3,5,7)
    marginals = [F(sum(x%d==0 for x in carrier),105) for d in ds]
    pairs = {(i,j):F(sum(x%ds[i]==0 and x%ds[j]==0 for x in carrier),105)
             for i in range(3) for j in range(i+1,3)}
    joint = F(sum(all(x%d==0 for d in ds) for x in carrier),105)
    require(joint == 0 and all(v>0 for v in pairs.values()),
            'Actual survivor permits every pair and forbids the triple')
    require(all(tree_mass(marginals,pairs,c)>0 for c in range(3)),
            'Every survivor pair-tree proxy remains positive')
    return dict(old_period=105, original_period=period,
                original_memberships=period*len(rows), private_checks=len(rows)**2,
                survivor_mass='104/105', actual_joint=str(joint),
                positive_tree_proxies=3)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--heights', nargs='+', type=int, default=[2,3,12])
    args = parser.parse_args()
    for height in args.heights:
        print(original_cut(height))
    print(boundary_bit_law())
    print(survivor_restriction())
    print('PASS exact old-cylinder, normalized-cut and boundary-law checks')


if __name__ == '__main__':
    main()
