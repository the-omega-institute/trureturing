#!/usr/bin/env python3
"""Solve the AP-family decision MILP for one N and report solver statuses."""

import argparse
from array import array
import json
from itertools import combinations
from math import inf
import os

for key in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS',
            'VECLIB_MAXIMUM_THREADS'):
    os.environ[key] = '1'

from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def is_ap(mask):
    if not mask:
        return False
    points = [i for i in range(mask.bit_length()) if mask >> i & 1]
    return len(points) < 3 or len({b - a for a, b in zip(points, points[1:])}) == 1


def vertices(n):
    result = []
    for k in (2, 3):
        result.extend(sum(1 << x for x in subset)
                      for subset in combinations(range(n), k))
    for d in range(1, (n - 1) // 3 + 1):
        for a in range(n - 3 * d):
            mask = 0
            for x in range(a, n, d):
                mask |= 1 << x
                if x >= a + 3 * d:
                    result.append(mask)
    assert len(result) == len(set(result))
    return result


def verify_witness(n, selected):
    target = n * (n - 1) // 2 + 2 + (n - 1) // 4
    assert len(selected) >= target and len(selected) == len(set(selected))
    assert not set.intersection(*(set(i for i in range(n) if mask >> i & 1)
                                  for mask in selected))
    assert all(bin(mask).count('1') <= 3 or is_ap(mask) for mask in selected)
    assert all(is_ap(a & b) for a, b in combinations(selected, 2))


def category(mask):
    return bin(mask).count("1")


def solve(n, mode, c, seconds, threads):
    all_vertices = vertices(n)
    if mode == "star":
        vs = [m for m in all_vertices
              if (category(m) != 3 or m >> c & 1) and
              (n < 27 or category(m) != 2 or m >> c & 1)]
    else:
        vs = all_vertices
    sizes = [category(m) for m in vs]
    nonap_triple = [s == 3 and not (lambda xs: xs[1]-xs[0] == xs[2]-xs[1])(
        [i for i in range(n) if m >> i & 1]) for m, s in zip(vs, sizes)]
    z = {}
    for i, (m, s) in enumerate(zip(vs, sizes)):
        if s >= 4:
            xs = [x for x in range(n) if m >> x & 1]
            d = xs[1] - xs[0]
            for p in xs:
                z.setdefault((d, p), len(vs) + len(z))
    rows, cols, data = array("i"), array("i"), array("b")
    edges = 0
    for i, a in enumerate(vs):
        si = sizes[i]
        bad_tri = nonap_triple[i]
        for j in range(i + 1, len(vs)):
            b = vs[j]
            inter = a & b
            if inter == 0 or (si == 3 and sizes[j] >= 4 and
                              inter == a and bad_tri):
                rows.extend((edges, edges))
                cols.extend((i, j))
                data.extend((1, 1))
                edges += 1
    extras_lo, extras_hi = [], []

    def add(entries, low, high):
        row = edges + len(extras_lo)
        for col, coefficient in entries:
            rows.append(row)
            cols.append(col)
            data.append(coefficient)
        extras_lo.append(low)
        extras_hi.append(high)

    target = n * (n - 1) // 2 + 2 + (n - 1) // 4
    add(((i, 1) for i in range(len(vs))), target, inf)
    add(((i, 1) for i, s in enumerate(sizes) if s == 2), -inf, n - 1)
    if mode == "nonstar":
        add(((i, 1) for i, s in enumerate(sizes) if s == 3), -inf, 3*n-8)
        for point in range(n):
            add(((i, 1) for i, s in enumerate(sizes)
                 if s == 3 and not (vs[i] >> point & 1)), 1, inf)
    else:
        add(((i, 1) for i, s in enumerate(sizes)
             if s != 3 and not (vs[i] >> c & 1)), 1, inf)

    for d in range(1, (n - 1) // 3 + 1):
        points = [(p, j) for (e, p), j in z.items() if e == d]
        if not points:
            continue
        add(((j, 1) for _, j in points), -inf, 1)
        for i, (m, s) in enumerate(zip(vs, sizes)):
            if s >= 4:
                xs = [x for x in range(n) if m >> x & 1]
                if xs[1] - xs[0] == d:
                    add([(i, 1)] + [(z[d, p], -1) for p in xs], -inf, 0)

    shape = (edges + len(extras_lo), len(vs) + len(z))
    matrix = coo_matrix((data, (rows, cols)), shape=shape).tocsr()
    lo = [-inf] * edges + extras_lo
    hi = [1] * edges + extras_hi
    print(f"BUILD N={n} mode={mode} c={c+1 if c is not None else 0} "
          f"vertices={len(vs)} edges={edges} rows={shape[0]}", flush=True)
    objective = [-1] * len(vs) + [0] * len(z)
    result = milp(objective, integrality=[1] * len(objective),
                  bounds=Bounds([0] * len(objective), [1] * len(objective)),
                  constraints=LinearConstraint(matrix, lo, hi),
                  options={"time_limit": seconds,
                           "mip_rel_gap": 0.0, "threads": threads})
    status = "infeasible" if result.status == 2 else "timeout" if result.status == 1 else "error"
    if result.x is not None:
        selected = [m for i, m in enumerate(vs) if result.x[i] > .5]
        if len(selected) >= target:
            verify_witness(n, selected)
            status = "feasible"
    print("CASE_RESULT " + json.dumps({"N": n, "mode": mode,
          "c": None if c is None else c+1, "status": status,
          "solver_status": result.status,
          "witness": None if status != 'feasible' else
          [[i + 1 for i in range(n) if mask >> i & 1] for mask in selected]}), flush=True)
    return status


def solve_full(n, seconds, threads):
    vs = vertices(n)
    edges = [(i, j) for i, a in enumerate(vs) for j in range(i + 1, len(vs))
             if not is_ap(a & vs[j])]
    rows, cols, data, lo, hi = [], [], [], [], []

    def add(indices, low, high):
        row = len(lo)
        for i in indices:
            rows.append(row)
            cols.append(i)
            data.append(1)
        lo.append(low)
        hi.append(high)

    for i, j in edges:
        add((i, j), -inf, 1)
    target = n * (n - 1) // 2 + 2 + (n - 1) // 4
    add(range(len(vs)), target, inf)
    for point in range(n):
        add((i for i, mask in enumerate(vs) if not mask >> point & 1), 1, inf)
    matrix = coo_matrix((data, (rows, cols)), shape=(len(lo), len(vs))).tocsr()
    print(f'BUILD N={n} mode=full vertices={len(vs)} edges={len(edges)} '
          f'rows={len(lo)}', flush=True)
    result = milp([-1] * len(vs), integrality=[1] * len(vs),
                  bounds=Bounds([0] * len(vs), [1] * len(vs)),
                  constraints=LinearConstraint(matrix, lo, hi),
                  options={'time_limit': seconds,
                           'mip_rel_gap': 0.0, 'threads': threads})
    status = 'infeasible' if result.status == 2 else 'timeout' if result.status == 1 else 'error'
    selected = []
    if result.x is not None:
        selected = [mask for i, mask in enumerate(vs) if result.x[i] > .5]
        if len(selected) >= target:
            verify_witness(n, selected)
            status = 'feasible'
    print('CASE_RESULT ' + json.dumps({'N': n, 'mode': 'full', 'c': None,
          'status': status, 'solver_status': result.status,
          'witness': None if status != 'feasible' else
          [[i + 1 for i in range(n) if mask >> i & 1] for mask in selected]}), flush=True)
    return status


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=13,
                        help='one N per invocation (13..18; default: 13)')
    parser.add_argument('--seconds', type=float, default=10800,
                        help='time limit per solver case in seconds (positive; default: 10800)')
    parser.add_argument('--threads', type=int, default=1,
                        help='HiGHS thread limit (1..12; default: 1)')
    try:
        args = parser.parse_args()
        if not 13 <= args.n <= 18 or args.seconds <= 0 or not 1 <= args.threads <= 12:
            parser.error('N must be 13..18, seconds positive, and threads 1..12')
    except SystemExit as exc:
        if exc.code:
            print('RESULT case-milp status=fail error=invalid_arguments')
        raise
    try:
        if args.n == 13:
            statuses = [solve_full(args.n, args.seconds, args.threads)]
        else:
            statuses = [solve(args.n, 'nonstar', None, args.seconds, args.threads)]
            for c in range((args.n + 1) // 2):
                statuses.append(solve(args.n, 'star', c, args.seconds, args.threads))
        assert all(status == 'infeasible' for status in statuses), statuses
    except Exception as exc:
        print(f'RESULT case-milp N={args.n} status=fail error={type(exc).__name__}: {exc}')
        raise SystemExit(1) from exc
    print(f'RESULT case-milp N={args.n} cases={len(statuses)} status=ok')


if __name__ == '__main__':
    main()
