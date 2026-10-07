#!/usr/bin/env python3
"""Exact rational lower certificate for Report573's product/deletion sources.

The certificate partitions the entire closed column-parameter simplex.
Each leaf carries a nonnegative query dual valid throughout its triangle.
This consumer uses no optimizer or third-party package.
"""
from fractions import Fraction as F
import json
from pathlib import Path


FAMILY = ((3, 2), (5, 4), (15, 0), (45, 1))
QUERIES = (3, 5, 9, 15, 45)
GAMMA = (F(1), F(5, 4), F(3, 2), F(5, 4), F(15, 8))
TARGET = F(23, 16)
REPRESENTATIVES = (
    ((0, 1), (1, 0)),
    ((1, 0), (0, 1), (0, 2)),
    ((0, 1), (1, 0), (4, 0)),
    ((0, 1), (0, 2), (1, 0), (4, 1), (1, 2)),
    ((0, 1), (0, 2), (1, 0), (1, 2), (4, 0), (4, 1), (4, 2)),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def literal_model():
    cells = {n: (n % 9, n % 5) for n in range(45)
             if all(n % modulus != residue for modulus, residue in FAMILY)}
    require(len(cells) == 20, "literal survivor count")
    inverse = {cell: n for n, cell in cells.items()}

    def coefficient_row(d, phase):
        row = [[0] * 3 for _ in range(3)]
        for n, (t, x) in cells.items():
            if n % d == phase:
                i = 0 if t in (0, 3, 6) else (1 if t == 1 else 2)
                j = x if x < 2 else 2
                row[i][j] += 1
        return tuple(tuple(r) for r in row)

    loads = []
    for d, representatives in zip(QUERIES, REPRESENTATIVES):
        rows = tuple(coefficient_row(d, inverse[c] % d)
                     for c in representatives)
        complete = {coefficient_row(d, a) for a in range(d)}
        complete.discard(((0, 0, 0),) * 3)
        require(set(rows) == complete and len(rows) == len(complete),
                f"complete distinct coefficient menu modulo {d}")
        loads.append(rows)
    mass = coefficient_row(1, 0)
    require(mass == ((0, 3, 6), (1, 0, 2), (2, 2, 4)), "source mass")
    return cells, tuple(loads), mass


def verify(certificate):
    require(set(certificate) == {"target", "roots", "nodes"}, "certificate fields")
    require(F(certificate["target"]) == TARGET, "lower target")
    cells, loads, mass = literal_model()
    flat = tuple(row for group in loads for row in group)
    nodes, roots = certificate["nodes"], certificate["roots"]
    require(len(roots) == 3, "three initial triangles")
    visited = set()
    leaf_count = 0
    inequality_count = 0
    max_depth = 0

    def visit(index, triangle, depth):
        nonlocal leaf_count, inequality_count, max_depth
        require(type(index) is int and 0 <= index < len(nodes), "node index")
        require(index not in visited, "cycle or shared node")
        visited.add(index)
        max_depth = max(max_depth, depth)
        node = nodes[index]
        if set(node) == {"dual"}:
            dual = tuple(F(x) for x in node["dual"])
            require(len(dual) == len(flat), "dual length")
            require(all(x >= 0 for x in dual), "nonnegative dual")
            offset = 0
            for group, budget in zip(loads, GAMMA):
                require(sum(dual[offset:offset + len(group)], F(0)) == budget,
                        "query weight budget")
                offset += len(group)
            for vertex in triangle:
                for i in range(3):
                    value = sum((dual[j] * sum(
                        (flat[j][i][k] * vertex[k] for k in range(3)), F(0))
                        for j in range(len(flat))), F(0))
                    required = TARGET * sum(
                        (mass[i][k] * vertex[k] for k in range(3)), F(0))
                    require(value >= required, "vertex/row coefficient bound")
                    inequality_count += 1
            leaf_count += 1
            return
        require(set(node) == {"edge", "children"}, "split node fields")
        edge = node["edge"]
        require(len(edge) == 2 and all(type(i) is int for i in edge), "edge indices")
        i, j = edge
        require(0 <= i < j < 3, "distinct ordered edge vertices")
        require(len(node["children"]) == 2, "two children")
        k = 3 - i - j
        midpoint = tuple((a + b) / 2 for a, b in zip(triangle[i], triangle[j]))
        visit(node["children"][0], (triangle[k], triangle[i], midpoint), depth + 1)
        visit(node["children"][1], (triangle[k], midpoint, triangle[j]), depth + 1)

    basis = tuple(tuple(F(int(i == j)) for j in range(3)) for i in range(3))
    center = (F(1, 3),) * 3
    for i, root in enumerate(roots):
        visit(root, (center, basis[i], basis[(i + 1) % 3]), 0)
    require(len(visited) == len(nodes), "unvisited certificate node")

    def norm(law):
        return sum((g * max(sum((law[n] for n in cells if n % d == a), F(0))
                            for a in range(d)) for d, g in zip(QUERIES, GAMMA)), F(0))

    joint = {n: F(1, 36) if t in (4, 7) and x in (2, 3) else F(1, 18)
             for n, (t, x) in cells.items()}
    product = {n: F(1, 24) if t in (4, 7) else F(1, 18)
               for n, (t, _) in cells.items()}
    require(sum(joint.values()) == sum(product.values()) == 1, "attainer normalization")
    require(norm(joint) == F(203, 144), "existing joint attainer")
    require(norm(product) == F(13, 9), "existing product upper witness")
    require(TARGET - norm(joint) == F(1, 36), "quantitative source-class gap")
    require(norm(product) - TARGET == F(1, 144), "remaining optimum interval")
    return {"lower": str(TARGET), "upper": "13/9", "joint_optimum": "203/144",
            "gap_lower": "1/36", "nodes": len(nodes), "leaves": leaf_count,
            "vertex_row_inequalities": inequality_count, "max_depth": max_depth}


if __name__ == "__main__":
    path = Path(__file__).with_name("free_product_prior_gap_certificate.json")
    print(json.dumps(verify(json.loads(path.read_text())), sort_keys=True))
