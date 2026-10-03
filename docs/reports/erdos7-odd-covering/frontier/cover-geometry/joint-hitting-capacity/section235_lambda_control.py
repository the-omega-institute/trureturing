#!/usr/bin/env python3
"""Exact joint hitting-capacity control for the Q/H=15 part of Section 235.

This is a finite source-compatible diagnostic.  The eleven classes are the
old Section 235 family, H=49 and Q=735.  It deliberately reports the empty
whole-cover fibres and never treats the local r=0 calculation as a cover.
"""

from __future__ import annotations

import json
from itertools import combinations
from math import gcd, lcm
from pathlib import Path


CLASSES = (
    (0, 3), (0, 5), (1, 7), (8, 15), (7, 21), (14, 35),
    (2, 49), (77, 105), (11, 147), (4, 245), (686, 735),
)
H = 49


def induced_residue(a: int, m: int, r: int) -> int:
    g = gcd(m, H)
    ell = m // g
    assert (a - r) % g == 0
    return ((a - r) // g * pow(H // g, -1, ell)) % ell


def components(ells: dict[int, int]) -> list[list[int]]:
    external = [i for i, ell in ells.items() if ell > 1]
    graph = {i: set() for i in external}
    for i, j in combinations(external, 2):
        if gcd(ells[i], ells[j]) > 1:
            graph[i].add(j)
            graph[j].add(i)
    result: list[list[int]] = []
    seen: set[int] = set()
    for root in external:
        if root in seen:
            continue
        todo = [root]
        seen.add(root)
        component: list[int] = []
        while todo:
            i = todo.pop()
            component.append(i)
            for j in graph[i]:
                if j not in seen:
                    seen.add(j)
                    todo.append(j)
        result.append(sorted(component))
    return result


def fibre_data(r: int, ells: dict[int, int], comps: list[list[int]]) -> tuple[bool, list[dict], list[list[int]]]:
    internal = all((r - a) % m for i, (a, m) in enumerate(CLASSES) if ells[i] == 1)
    data: list[dict] = []
    empty: list[list[int]] = []
    if not internal:
        return False, data, empty
    for component in comps:
        period = 1
        for i in component:
            period = lcm(period, ells[i])
        active: list[tuple[int, int]] = []
        for i in component:
            a, m = CLASSES[i]
            if (a - r) % gcd(m, H) == 0:
                active.append((i, induced_residue(a, m, r)))
        remainder = [
            t for t in range(period)
            if not any((t - b) % ells[i] == 0 for i, b in active)
        ]
        if not remainder:
            empty.append(component)
        private: dict[int, set[int]] = {}
        for i, b in active:
            private[i] = {
                t for t in range(period) if (t - b) % ells[i] == 0
                and all((t - b2) % ells[j] != 0
                        for j, b2 in active if j != i)
            }
        data.append({
            "component": component,
            "period": period,
            "active": active,
            "remainder": remainder,
            "private": private,
        })
    return True, data, empty


def coordinates(ells: dict[int, int]) -> dict[tuple[int, int], set[int]]:
    result: dict[tuple[int, int], set[int]] = {}
    for i, value in ells.items():
        p = 2
        while p * p <= value:
            depth = 1
            while value % p == 0:
                result.setdefault((p, depth), set()).add(i)
                value //= p
                depth += 1
            p += 1
        if value > 1:
            result.setdefault((value, 1), set()).add(i)
    return result


def minimum_subset(
    universe: list[int],
    sets: list[set[int]],
    capacities: dict[int, int],
    demand: int,
    require_capacity: bool,
) -> int | None:
    for size in range(len(universe) + 1):
        for chosen in combinations(universe, size):
            subset = set(chosen)
            if not all(subset & target for target in sets):
                continue
            if require_capacity and sum(capacities.get(r, 0) for r in subset) < demand:
                continue
            return size
    return None


def main() -> None:
    q = 1
    for _, modulus in CLASSES:
        q = lcm(q, modulus)
    ells = {i: modulus // gcd(modulus, H) for i, (_, modulus) in enumerate(CLASSES)}
    comps = components(ells)
    rows = []
    for r in range(H):
        usable, data, empty = fibre_data(r, ells, comps)
        if usable:
            rows.append((r, data, empty))

    singleton = [r for r, _, empty in rows if len(empty) == 1]
    empty_rows = [r for r, _, empty in rows if not empty]

    e_sets: dict[int, set[int]] = {i: set() for i, ell in ells.items() if ell > 1}
    cap: dict[tuple[int, int], dict[int, int]] = {}
    coord = coordinates(ells)
    for r, data, empty in rows:
        if len(empty) != 1:
            continue
        empty_index = next(k for k, item in enumerate(data) if item["component"] == empty[0])
        sink_capacity = 1
        for k, item in enumerate(data):
            if k != empty_index:
                sink_capacity *= len(item["remainder"])
        item = data[empty_index]
        for i, private in item["private"].items():
            if private:
                e_sets[i].add(r)
        for v, labels in coord.items():
            labels_here = labels & set(item["component"])
            if not labels_here:
                continue
            adjacent = {
                t for t in range(item["period"])
                if any(t in item["private"].get(i, set()) for i in labels_here)
            }
            cap.setdefault(v, {})[r] = sink_capacity * len(adjacent)

    full_records = []
    for v, labels in sorted(coord.items()):
        labels = sorted(labels)
        if not labels:
            continue
        sets = [e_sets[i] for i in labels]
        tau = minimum_subset(singleton, sets, {}, len(labels), False)
        capacities = cap.get(v, {})
        kappa = None
        for size in range(len(singleton) + 1):
            values = sorted((capacities.get(r, 0) for r in singleton), reverse=True)
            if sum(values[:size]) >= len(labels):
                kappa = size
                break
        lam = minimum_subset(singleton, sets, capacities, len(labels), True)
        full_records.append({
            "coordinate": list(v),
            "labels": labels,
            "tau": tau,
            "kappa": kappa,
            "lambda": lam,
        })

    # Restrict to the one covered fibre and the labels active there.  This is
    # a local control only; it is not the complete I_H flow.
    r0, data0, empty0 = next(row for row in rows if row[0] == 0)
    component0 = next(item for item in data0 if item["component"] == empty0[0])
    active0 = sorted(i for i, _ in component0["active"] if component0["private"].get(i))
    local_records = []
    local_weighted_lambda = 0
    local_budget = len(active0) - 1
    for v, labels in sorted(coord.items()):
        labels = sorted(set(labels) & set(active0))
        if not labels:
            continue
        sets = [{0} for _ in labels]
        capacities = {0: len({
            t for t in range(component0["period"])
            if any(t in component0["private"].get(i, set()) for i in labels)
        })}
        lam = minimum_subset([0], sets, capacities, len(labels), True)
        weight = v[0] - 1
        local_weighted_lambda += weight * lam
        local_records.append({"coordinate": list(v), "labels": labels, "lambda": lam})

    assert q == 735 and len(rows) == 41 and singleton == [0]
    assert len(empty_rows) == 40
    assert all(row["lambda"] is None for row in full_records)
    assert local_weighted_lambda == 6 and local_budget == 6

    result = {
        "schema": "section235-joint-hitting-capacity-v1",
        "Q": q,
        "H": H,
        "Q_over_H": q // H,
        "usable_fibres": len(rows),
        "singleton_empty_component_fibres": singleton,
        "empty_component_fibres": empty_rows,
        "full_coordinate_records": full_records,
        "local_r0_active_labels": active0,
        "local_r0_weighted_lambda": local_weighted_lambda,
        "local_r0_budget": local_budget,
        "local_r0_records": local_records,
        "scope": (
            "The full I_H flow is impossible: two coordinates have lambda=+infinity "
            "and forty usable fibres have no empty component. The finite r=0 values "
            "are a local diagnostic only; they do not assert whole coverage."
        ),
    }
    output = Path(__file__).with_suffix(".json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
