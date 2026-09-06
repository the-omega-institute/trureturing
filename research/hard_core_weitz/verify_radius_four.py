#!/usr/bin/env python3
"""Replay the Lean-owned radius-four certificate with exact integer geometry.

No eigensolver, discovery cache, saved verdict or third-party package is used.
Additional finite regressions exercise the mathematical refinement/light-cone
statements; they are not proofs of their universal claims or Lean proof checks.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import random
import re
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BUCKET = ROOT / "D5/S3/StatisticalMechanics/HardCore"
DATA = BUCKET / "RadiusFourData.lean"
CERT = BUCKET / "RadiusFourCertificates.lean"
POINTS = [(x, y) for x in range(-4, 5) for y in range(-4, 5)
          if 0 < abs(x) + abs(y) <= 4] + [(0, 0)]
DIRECTIONS = ((1, 0), (0, -1), (0, 1))
ORDERS = tuple(itertools.permutations(range(3)))
PARENT = frozenset({(-1, 0)})


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def moved(p: tuple[int, int], d: int) -> tuple[int, int]:
    x, y = p
    return ((x - 1, y), (-y - 1, x), (y - 1, -x))[d]


def deleted(a: int, d: int) -> frozenset:
    return frozenset({(0, 0)} | {DIRECTIONS[e] for e in ORDERS[a][:ORDERS[a].index(d)]})


@lru_cache(None)
def update(radius: int | None, blocked: frozenset, a: int, d: int) -> frozenset:
    image = frozenset(moved(p, d) for p in blocked | deleted(a, d))
    return image if radius is None else frozenset(p for p in image if sum(map(abs, p)) <= radius)


def read_rows() -> list[tuple[int, int]]:
    text = DATA.read_text()
    weights_text = text.split("private def weightClasses", 1)[1].split("[", 1)[1].split("]", 1)[0]
    weights = list(map(int, re.findall(r"\d+", weights_text)))
    packed_text = text.split("private def packedRows", 1)[1].split("[", 1)[1].split("]", 1)[0]
    packed = list(map(int, re.findall(r"\d+", packed_text)))
    rows = []
    for code in packed:
        mask, index = code % (1 << 41), code // (1 << 41)
        require(index < len(weights), "weight-class range")
        rows.append((mask, weights[index]))
    literal = CERT.read_text().split("private def pointList", 1)[1].split("]", 1)[0]
    require([tuple(map(int, p)) for p in re.findall(r"\((-?\d+),(-?\d+)\)", literal)] == POINTS,
            "Lean coordinate order")
    return rows


def audit(rows: list[tuple[int, int]], omit_origin: bool = False) -> tuple[list, dict]:
    require(len(rows) == 851, "row cardinality")
    codes = [r[0] for r in rows]
    require(len(set(codes)) == 851 and codes[0] == 4096, "unique masks and initial mask")
    masks = [frozenset(p for k, p in enumerate(POINTS) if code & (1 << k)) for code in codes]
    require(all((-1, 0) in f and (0, 0) not in f for f in masks), "parent and origin")
    index = {f: i for i, f in enumerate(masks)}
    edges = []
    for i, f in enumerate(masks):
        children = []
        for d in range(3):
            if DIRECTIONS[d] in f:
                children.append(None)
                continue
            kills = deleted(0, d) - ({(0, 0)} if omit_origin else set())
            image = {moved(p, d) for p in f | kills}
            g = frozenset(p for p in image if sum(map(abs, p)) <= 4)
            require(g in index, f"missing geometric successor {i},{d}")
            children.append(index[g])
        edges.append(children)
    slacks = []
    for i, (_, w) in enumerate(rows):
        require(1 <= w <= 20000, f"weight range {i}")
        slack = 24827 * w - 10000 * sum(rows[j][1] for j in edges[i] if j is not None)
        require(slack >= 0, f"upper row {i}")
        slacks.append(slack)
    require(rows[0][1] == 20000, "root weight")
    seen, pending = {0}, [0]
    for i in pending:
        for j in edges[i]:
            if j is not None and j not in seen:
                seen.add(j)
                pending.append(j)
    require(len(seen) == 851, "complete fixed-order reachability")
    return edges, {"states": len(rows), "reachable_states": len(seen),
                   "geometric_move_checks": len(rows) * 3, "integer_row_checks": len(rows),
                   "root_weight": rows[0][1], "minimum_integer_slack": min(slacks),
                   "distinct_weights": len({w for _, w in rows})}


@lru_cache(None)
def fixed_count(radius: int | None, n: int, blocked: frozenset, a: int = 0) -> int:
    if n == 0:
        return 1
    return sum(fixed_count(radius, n - 1, update(radius, blocked, a, d), a)
               for d in range(3) if DIRECTIONS[d] not in blocked)


def history_count(radius: int | None, n: int, h: tuple, blocked: frozenset, policy) -> int:
    if n == 0:
        return 1
    a = policy(h, blocked)
    return sum(history_count(radius, n-1, (d,) + h, update(radius, blocked, a, d), policy)
               for d in range(3) if DIRECTIONS[d] not in blocked)


def coupled_count(r: int, R: int, n: int, h: tuple, F: frozenset, G: frozenset, policy) -> int:
    if n == 0:
        return 1
    a = policy(h, F)
    return sum(coupled_count(r, R, n-1, (d,) + h, update(r, F, a, d),
                             update(R, G, a, d), policy)
               for d in range(3) if DIRECTIONS[d] not in G)


def exact_regressions(rows: list[tuple[int, int]], edges: list) -> dict:
    counts, depth_tests = [1] * len(rows), 0
    for n in range(101):
        for i, (_, w) in enumerate(rows):
            require(10000**n * counts[i] <= 24827**n * w, f"table depth {n},{i}")
            depth_tests += 1
        counts = [sum(counts[j] for j in es if j is not None) for es in edges]
    radius_tests = 0
    for p in itertools.product(range(-12, 13), repeat=2):
        for d in range(3):
            require(sum(map(abs, p)) <= sum(map(abs, moved(p, d))) + 1, "radius speed")
            radius_tests += 1
    rng = random.Random(20260906)
    disk = [p for p in itertools.product(range(-4, 5), repeat=2) if sum(map(abs, p)) <= 4]
    monotone_tests = coupled_tests = light_tests = block_tests = 0
    policy = lambda h, F: (len(F) + 2*sum(h) + len(h)) % 6
    history_policy = lambda h, _: (sum((k+1)*d for k, d in enumerate(h)) + len(h)) % 6
    for _ in range(60):
        G = frozenset(p for p in disk if rng.randrange(4) == 0)
        F = frozenset(p for p in G if rng.randrange(2) == 0)
        r = rng.randrange(1, 5)
        R = r + rng.randrange(3)
        for a in range(6):
            for d in range(3):
                require(update(r, F, a, d) <= update(R, G, a, d), "monotone memory")
                monotone_tests += 1
        n = rng.randrange(1, 6)
        require(coupled_count(r, R, n, (), F, G, policy) <= history_count(r, n, (), F, policy),
                "coupled controller")
        require(history_count(R, n, (), G, history_policy) <= history_count(r, n, (), F, history_policy),
                "common history controller")
        coupled_tests += 2
    for n in range(7):
        for extra in range(3):
            r = max(1, n + extra)
            for trial in range(6):
                common = frozenset(p for p in disk if sum(map(abs, p)) <= n and rng.randrange(5) == 0)
                F = common | frozenset({(n+2, trial+1)})
                G = common | frozenset({(-n-3, trial+2), (n+5, -trial)})
                require(history_count(r, n, (), F, history_policy) ==
                        history_count(None, n, (), G, history_policy), "finite-horizon exactness")
                light_tests += 1
    for r in range(1, 6):
        for k in range(1, r+1):
            for a in range(6):
                C = fixed_count(None, k, PARENT, a)
                for q in range(3):
                    for s in range(k):
                        if q*k+s > 8:
                            continue
                        F = PARENT | frozenset({(0, 1)})
                        require(fixed_count(r, q*k+s, F, a) <= C**q * 3**s, "uniform block")
                        block_tests += 1
    F = G = PARENT
    for d in (0, 0, 1, 1):
        require(DIRECTIONS[d] not in F and DIRECTIONS[d] not in G, "counterhistory legality")
        F, G = update(3, F, 0, d), update(4, G, 0, d)
    require((2, -1) not in F and (2, -1) in G, "coarse projection counterexample")
    return {"table_depth_checks": depth_tests, "radius_speed_checks": radius_tests,
            "memory_monotonicity_checks": monotone_tests, "controller_count_checks": coupled_tests,
            "light_cone_checks": light_tests, "uniform_block_checks": block_tests,
            "projection_counterhistory": [0, 0, 1, 1], "extra_fine_blocker": [2, -1]}


def actual_domain_regressions() -> dict:
    @lru_cache(None)
    def count(n: int, V: frozenset, F: frozenset) -> int:
        require(V.isdisjoint(F), "actual-domain blocker disjointness")
        if n == 0:
            return 1
        result = 0
        for d in range(3):
            if DIRECTIONS[d] not in V:
                continue
            require(DIRECTIONS[d] not in F, "actual child suppressed")
            Vnext = frozenset(moved(p, d) for p in V - deleted(0, d))
            result += count(n-1, Vnext, update(4, F, 0, d))
        return result
    tests = 0
    for r in range(1, 4):
        square = frozenset(p for p in itertools.product(range(-r, r+1), repeat=2) if p != (-1, 0))
        for variant in range(3):
            V = frozenset(p for p in square if variant == 0 or (p[0] + 2*p[1]) % (variant+2) != 1)
            for n in range(10):
                value = count(n, V, PARENT)
                require(10000**n * value <= 20000 * 24827**n, "finite-domain bound")
                require(value <= fixed_count(4, n, PARENT), "finite-domain simulation")
                tests += 1
    return {"finite_domain_checks": tests}


def negative_controls(rows: list[tuple[int, int]]) -> dict:
    wrong_weight = rows.copy()
    wrong_weight[0] = (rows[0][0], 1)
    cases = [("missing-state", rows[:-1], False), ("duplicate-mask", [rows[0]]+rows[:-1], False),
             ("wrong-upper-weight", wrong_weight, False), ("omitted-origin", rows, True)]
    errors = {}
    for name, data, omit in cases:
        try:
            audit(data, omit)
        except ValueError as error:
            errors[name] = str(error)
        else:
            raise ValueError(f"accepted corruption: {name}")
    failures = [n for n in range(1, 9) if fixed_count(1, n, PARENT) != fixed_count(None, n, PARENT)]
    require(bool(failures), "missing finite-depth guard negative control")
    errors["radius-smaller-than-depth"] = {"first_tested_mismatch_depth": failures[0]}
    return errors


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    rows = read_rows()
    edges, result = audit(rows)
    result.update(exact_regressions(rows, edges))
    result.update(actual_domain_regressions())
    require(20000 * 24827**700 < 25205**700, "finite universal separation arithmetic")
    result["integer_separation_depth"] = 700
    result["negative_controls"] = negative_controls(rows)
    result["data_sha256"] = hashlib.sha256(DATA.read_bytes()).hexdigest()
    result["verifier_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result["lean_compilation"] = "not executed; independent integer and set replay only"
    text = json.dumps(result, indent=2) + "\n"
    print(text, end="")
    if args.output:
        args.output.write_text(text)


if __name__ == "__main__":
    main()
