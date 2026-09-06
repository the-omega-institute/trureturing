#!/usr/bin/env python3
"""Exact research replay of the Lean-owned radius-three data.

Run from the repository root. Uses Python integers and geometric sets only.
No floating-point eigensolver, NumPy, discovery cache, or stored verdict is read.
This is independent implementation replay, not independent-author review or Lean.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import json
import re
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BUCKET = ROOT / "D5/S3/StatisticalMechanics/HardCore"
DATA = BUCKET / "RadiusThreeData.lean"
POINTS = [(x, y) for x in range(-3, 4) for y in range(-3, 4)
          if 0 < abs(x) + abs(y) <= 3] + [(0, 0)]
DIRECTIONS = [(1, 0), (0, -1), (0, 1)]
ORDERS = list(itertools.permutations(range(3)))
CAP = 10**9
Row = tuple[int, int, int, int, int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_rows() -> list[Row]:
    source = DATA.read_text()
    weight_text = source.split("private def weightClasses", 1)[1].split("]", 1)[0]
    classes = [tuple(map(int, m)) for m in re.findall(
        r"\((\d+), (\d+), (\d+)\)", weight_text)]
    code_text = source.split("private def packedRows", 1)[1].split("[", 1)[1].split("]", 1)[0]
    codes = list(map(int, re.findall(r"\d+", code_text)))
    result = []
    for code in codes:
        mask, tagged = code % 524288, code // 524288
        ordering, class_index = tagged % 6, tagged // 6
        require(class_index < len(classes), "weight-class range")
        result.append((mask, *classes[class_index], ordering))
    return result


def moved(p: tuple[int, int], d: int) -> tuple[int, int]:
    x, y = p
    return [(x - 1, y), (-y - 1, x), (y - 1, -x)][d]


def killed(a: int, d: int) -> set[tuple[int, int]]:
    before = ORDERS[a][:ORDERS[a].index(d)]
    return {(0, 0)} | {DIRECTIONS[e] for e in before}


def audit(rows: list[Row], *, omit_origin: bool = False) -> tuple[list, dict]:
    require(len(rows) == 483, "row cardinality")
    codes = [r[0] for r in rows]
    require(len(set(codes)) == 483 and codes[0] == 64, "unique masks and initial mask")
    masks = [frozenset(p for k, p in enumerate(POINTS) if code & (1 << k))
             for code in codes]
    require(all(code < 2**25 for code in codes), "mask range")
    require(all((-1, 0) in f and (0, 0) not in f for f in masks), "parent blockers")
    index = {f: i for i, f in enumerate(masks)}
    edges = []
    for i, f in enumerate(masks):
        actions = []
        for a in range(6):
            children = []
            for d, destination in enumerate(DIRECTIONS):
                if destination in f:
                    children.append(None)
                    continue
                dead = killed(a, d)
                if omit_origin:
                    dead.discard((0, 0))
                transformed = {moved(p, d) for p in f | dead}
                child = frozenset(p for p in transformed if abs(p[0]) + abs(p[1]) <= 3)
                require(child in index, f"missing geometric successor {i},{a},{d}")
                children.append(index[child])
            actions.append(children)
        edges.append(actions)
    for i, (_, lo, up, fix, policy) in enumerate(rows):
        require(0 <= lo <= CAP and 1 <= up and 0 <= fix <= CAP, f"weight range {i}")
        require(0 <= policy < 6, f"policy range {i}")
        for a in range(6):
            low_sum = sum(rows[j][1] for j in edges[i][a] if j is not None)
            require(5041 * lo <= 2000 * low_sum, f"all-policy lower row {i},{a}")
        upper_sum = sum(rows[j][2] for j in edges[i][policy] if j is not None)
        require(5000 * upper_sum <= 12603 * up, f"chosen upper row {i}")
        fixed_sum = sum(rows[j][3] for j in edges[i][0] if j is not None)
        require(25209 * fix <= 10000 * fixed_sum, f"fixed lower row {i}")
    require(rows[0][1:4] == (CAP, CAP, CAP), "initial weights")

    def reachable(policy: int | None, adaptive: bool = False) -> int:
        seen, pending = {0}, [0]
        while pending:
            i = pending.pop()
            actions = [rows[i][4]] if adaptive else (range(6) if policy is None else [policy])
            for a in actions:
                for j in edges[i][a]:
                    if j is not None and j not in seen:
                        seen.add(j)
                        pending.append(j)
        return len(seen)
    require(reachable(None) == 483, "full table is reachable")
    return edges, {"states": 483, "geometric_move_checks": 483 * 6 * 3,
                   "integer_row_checks": 483 * 8,
                   "adaptive_reachable": reachable(None, True),
                   "fixed_SRL_reachable": reachable(0)}


def count_regressions(rows: list[Row], edges: list) -> dict:
    adaptive = fixed = optimal = [1] * len(rows)
    for n in range(81):
        require(5000**n * adaptive[0] <= CAP * 12603**n, f"upper depth {n}")
        require(5041**n <= 2000**n * optimal[0], f"optimal lower depth {n}")
        require(25209**n <= 10000**n * fixed[0], f"fixed lower depth {n}")
        sums = lambda v, i, a: sum(v[j] for j in edges[i][a] if j is not None)
        adaptive = [sums(adaptive, i, r[4]) for i, r in enumerate(rows)]
        fixed = [sums(fixed, i, 0) for i in range(len(rows))]
        optimal = [min(sums(optimal, i, a) for a in range(6)) for i in range(len(rows))]
    return {"depth_regressions": 81 * 3}


def finite_domain_regressions(rows: list[Row], edges: list) -> dict:
    @lru_cache(None)
    def actual(n: int, domain: frozenset, state: int) -> int:
        if n == 0:
            return 1
        a = rows[state][4]
        total = 0
        for d, destination in enumerate(DIRECTIONS):
            if destination not in domain:
                continue
            j = edges[state][a][d]
            require(j is not None, "actual child lost")
            nxt = frozenset(moved(p, d) for p in domain - killed(a, d))
            total += actual(n - 1, nxt, j)
        return total
    tests = 0
    for r in range(1, 4):
        square = frozenset((x, y) for x in range(-r, r+1) for y in range(-r, r+1)
                           if (x, y) != (-1, 0))
        for variant in range(3):
            domain = frozenset(p for p in square if variant == 0 or
                               (p[0] + 2*p[1]) % (variant+2) != 1)
            for n in range(9):
                require(5000**n * actual(n, domain, 0) <= CAP * 12603**n,
                        f"domain upper {r},{variant},{n}")
                tests += 1
    return {"finite_domain_regressions": tests}


def negative_controls(rows: list[Row]) -> dict:
    bad_upper = rows.copy()
    bad_upper[0] = (rows[0][0], rows[0][1], 1, rows[0][3], rows[0][4])
    bad_lower = rows.copy()
    bad_lower[1] = (rows[1][0], CAP, rows[1][2], rows[1][3], rows[1][4])
    bad_policy = [(m, lo, up, fix, 0) for m, lo, up, fix, _ in rows]
    tests = [("missing-state", rows[:-1], False), ("duplicate-mask", [rows[0]]+rows[:-1], False),
             ("wrong-upper-weight", bad_upper, False), ("wrong-lower-weight", bad_lower, False),
             ("erase-adaptation", bad_policy, False), ("omit-origin-deletion", rows, True)]
    failures = {}
    for name, altered, omit in tests:
        try:
            audit(altered, omit_origin=omit)
        except ValueError as error:
            failures[name] = str(error)
        else:
            raise ValueError(f"negative control was incorrectly accepted: {name}")
    return failures


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rows = read_rows()
    source = (BUCKET / "RadiusThreeCertificates.lean").read_text()
    point_text = source.split("private def pointList", 1)[1].split("]", 1)[0]
    literal_points = [tuple(map(int, p)) for p in re.findall(r"\((-?\d+),(-?\d+)\)", point_text)]
    require(literal_points == POINTS, "Lean point enumeration differs")
    edges, result = audit(rows)
    result.update(count_regressions(rows, edges))
    result.update(finite_domain_regressions(rows, edges))
    result["negative_controls"] = negative_controls(rows)
    result["data_sha256"] = hashlib.sha256(DATA.read_bytes()).hexdigest()
    result["lean_compilation"] = "not executed by this verifier"
    text = json.dumps(result, indent=2) + "\n"
    print(text, end="")
    if args.output:
        args.output.write_text(text)

if __name__ == "__main__":
    main()
