#!/usr/bin/env python3
"""Build fixed-centre clique LPs and verify exact rational primal/dual certificates."""

import argparse
import json
import os
from fractions import Fraction
from itertools import combinations

for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS',
            'VECLIB_MAXIMUM_THREADS'):
    os.environ[key] = '1'

import networkx as nx
from scipy.optimize import linprog
from scipy.sparse import csr_matrix


def is_ap(mask):
    points = [i for i in range(mask.bit_length()) if mask >> i & 1]
    return bool(points) and (len(points) < 3 or
                             len({b - a for a, b in zip(points, points[1:])}) == 1)


def long_aps(n):
    result = []
    for d in range(1, (n - 1) // 3 + 1):
        for a in range(n - 3 * d):
            mask = 0
            for b in range(a, n, d):
                mask |= 1 << b
                if b >= a + 3 * d:
                    result.append(mask)
    return result


def model(n, c):
    aps = long_aps(n)
    points = [x for x in range(n) if x != c]
    vertices = [('Q', mask) for mask in aps if mask >> c & 1]
    vertices += [('H', (1 << c) | (1 << x)) for x in points]
    vertices += [('T', (1 << c) | (1 << x) | (1 << y))
                 for x, y in combinations(points, 2)]
    vertices += [('A', mask) for mask in aps if not mask >> c & 1]
    graph = nx.Graph()
    graph.add_nodes_from(range(len(vertices)))
    graph.add_edges_from((i, j) for i, j in combinations(range(len(vertices)), 2)
                         if not is_ap(vertices[i][1] & vertices[j][1]))
    cliques = sorted(tuple(sorted(clique)) for clique in nx.find_cliques(graph))
    rows = [(clique, 1, 1) for clique in cliques]
    rows += [((i,), 1, 1) for i in range(len(vertices))]
    avoiders = tuple(i for i, (kind, _) in enumerate(vertices) if kind == 'A')
    if avoiders:
        rows.append((avoiders, -1, -1))
    return vertices, rows, avoiders


def matrix(rows, size):
    indptr, indices, values = [0], [], []
    for ids, coefficient, _ in rows:
        indices.extend(ids)
        values.extend([coefficient] * len(ids))
        indptr.append(len(indices))
    return csr_matrix((values, indices, indptr), shape=(len(rows), size), dtype=float)


def exact_certificate(result, rows, size):
    primal = [Fraction(float(x)).limit_denominator(10**7) for x in result.x]
    assert all(x >= 0 for x in primal)
    assert all(coefficient * sum(primal[i] for i in ids) <= bound
               for ids, coefficient, bound in rows)
    weights = {i: Fraction(-float(y)).limit_denominator(10**7)
               for i, y in enumerate(result.ineqlin.marginals) if y < -1e-8}
    coverage = [Fraction(0)] * size
    for row_index, weight in weights.items():
        ids, coefficient, _ = rows[row_index]
        for i in ids:
            coverage[i] += weight * coefficient
    singleton_start = len(rows) - size - 1
    for i, total in enumerate(coverage):
        if total < 1:
            row_index = singleton_start + i
            assert rows[row_index] == ((i,), 1, 1)
            weights[row_index] = weights.get(row_index, Fraction(0)) + 1 - total
            coverage[i] = Fraction(1)
    value = sum(weight * rows[i][2] for i, weight in weights.items())
    assert sum(primal) == value
    return primal, weights, value


def verify_exact(primal, weights, value, rows, size):
    assert len(primal) == size and all(x >= 0 for x in primal)
    for ids, coefficient, bound in rows:
        assert coefficient * sum(primal[i] for i in ids) <= bound
    coverage = [Fraction(0)] * size
    dual_value = Fraction(0)
    for row_index, weight in weights.items():
        assert 0 <= row_index < len(rows) and weight >= 0
        ids, coefficient, bound = rows[row_index]
        dual_value += weight * bound
        for i in ids:
            coverage[i] += weight * coefficient
    assert all(total >= 1 for total in coverage)
    assert sum(primal) == dual_value == value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--nmin', type=int, default=1,
                        help='first N (1..16; default: 1)')
    parser.add_argument('--nmax', type=int, default=16,
                        help='last N (1..16; default: 16)')
    parser.add_argument('--threads', type=int, default=1,
                        help='maximum CPU threads (1..12; HiGHS is run on one)')
    try:
        args = parser.parse_args()
        if not 1 <= args.nmin <= args.nmax <= 16 or not 1 <= args.threads <= 12:
            parser.error('N must satisfy 1 <= nmin <= nmax <= 16; threads must be 1..12')
    except SystemExit as exc:
        if exc.code:
            print('RESULT lp-certificates status=fail error=invalid_arguments')
        raise
    try:
        feasible, minimum_margin, strong = 0, None, []
        for n in range(args.nmin, args.nmax + 1):
            for c in range(n):
                vertices, rows, avoiders = model(n, c)
                if not avoiders:
                    continue
                result = linprog([-1] * len(vertices), A_ub=matrix(rows, len(vertices)),
                                 b_ub=[bound for _, _, bound in rows],
                                 bounds=(0, None), method='highs')
                assert result.status == 0, (n, c + 1, result.message)
                primal, weights, value = exact_certificate(result, rows, len(vertices))
                verify_exact(primal, weights, value, rows, len(vertices))
                target = n * (n - 1) // 2 + 1
                bound = target + (n - 1) // 4
                assert value <= bound, (n, c + 1, value, bound)
                margin = bound - value
                minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
                if value > target:
                    strong.append((n, c + 1, str(value - target)))
                if (n, c + 1) == (14, 7):
                    assert value == Fraction(1663, 18)
                feasible += 1
        if (args.nmin, args.nmax) == (1, 16):
            assert feasible == 121 and minimum_margin == 1
            assert strong[0] == (14, 7, '7/18')
        print(json.dumps({'verified': feasible, 'smallest_B_margin': str(minimum_margin),
                          'strong_target_failures': len(strong)}, sort_keys=True))
    except Exception as exc:
        print(f'RESULT lp-certificates status=fail error={type(exc).__name__}: {exc}')
        raise SystemExit(1) from exc
    print('RESULT lp-certificates status=ok')


if __name__ == '__main__':
    main()
