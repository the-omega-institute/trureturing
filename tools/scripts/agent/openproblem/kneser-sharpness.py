#!/usr/bin/env python3
"""Construct and check avoiding edge colourings for three small parameters."""

from itertools import combinations

from pysat.solvers import Glucose3


def check(n, k):
    vertices = list(combinations(range(1, n + 1), k))
    masks = [sum(1 << (p - 1) for p in member) for member in vertices]
    edges = {pair: i for i, pair in enumerate(combinations(range(len(vertices)), 2), 1)}
    triangles = []
    clauses = []
    for a, b, c in combinations(range(len(vertices)), 3):
        if masks[a] & masks[b] & masks[c]:
            continue
        edge_ids = (edges[(a,b)], edges[(a,c)], edges[(b,c)])
        triangles.append(edge_ids)
        clauses.extend((edge_ids, tuple(-i for i in edge_ids)))
    with Glucose3(bootstrap_with=clauses) as solver:
        if not solver.solve():
            raise RuntimeError(f"V({n},{k}) is UNSAT; no avoiding colouring constructed")
        positive = {lit for lit in solver.get_model() if lit > 0}
    assert all(not (set(triple) <= positive or set(triple).isdisjoint(positive))
               for triple in triangles)
    assert all(any((lit > 0) == (abs(lit) in positive) for lit in clause)
               for clause in clauses)
    print(f"V({n},{k}): SAT, {len(vertices)} vertices, {len(edges)} edges, "
          f"{len(triangles)} triangles, {len(positive)} red edges; colouring checked")


if __name__ == "__main__":
    for parameters in ((4,2),(5,3),(7,4)):
        check(*parameters)
