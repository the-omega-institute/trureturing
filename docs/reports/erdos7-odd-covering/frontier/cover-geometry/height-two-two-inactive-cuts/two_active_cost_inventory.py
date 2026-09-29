#!/usr/bin/env python3
"""Check the necessary normalized cost inventory for Report449, TA.1--TA.7.

This does not enumerate or certify actual sources. Whole-column private
prefixes retain their token cost three; they are not replaced by three leaves.
"""

import argparse
from fractions import Fraction
from itertools import combinations_with_replacement, product
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def inventory():
    rows = []
    for occupancies in ((5, 5), (4, 5)):
        active_ranges = (range(n - 2, n + 1) for n in occupancies)
        for active in product(*active_ranges):
            delta = sum(n - a for n, a in zip(occupancies, active))
            costs = (
                combinations_with_replacement(range(4), a) for a in active
            )
            for shapes in product(*costs):
                if occupancies == (5, 5) and (
                    active[0], shapes[0]
                ) > (active[1], shapes[1]):
                    continue
                totals = [sum(shape) for shape in shapes]
                least = [
                    sum(shape[:n - 2])
                    for shape, n in zip(shapes, occupancies)
                ]
                root_costs = [
                    7 * (n - a) + 2 * z
                    for n, a, z in zip(occupancies, active, totals)
                ]
                if max(root_costs) > 20:
                    continue
                for public_cost in range(6):
                    if public_cost == 0 and any(0 in shape for shape in shapes):
                        continue
                    if sum(least) < 9 - public_cost:
                        continue
                    capacity = 42 + 7 * (delta + public_cost) + 2 * sum(totals)
                    if capacity not in (77, 78):
                        continue
                    rows.append({
                        "n": occupancies, "a": active, "delta": delta,
                        "k": public_cost, "c": capacity,
                        "shape": ["".join(map(str, shape)) for shape in shapes],
                        "p": least, "Z": totals, "rootcost": root_costs,
                    })

    expected77 = {
        ((5, 5), (4, 5), 0, ("1111", "22222")),
        ((5, 5), (5, 5), 1, ("01111", "22222")),
        ((5, 5), (5, 5), 1, ("11111", "12222")),
        ((4, 5), (4, 5), 1, ("1111", "22222")),
    }
    expected78 = {
        ((5, 5), ("11123", "22222")),
        ((5, 5), ("11222", "12223")),
        ((5, 5), ("11222", "22222")),
        ((5, 5), ("11223", "12222")),
        ((5, 5), ("12222", "12222")),
        ((4, 5), ("1223", "22222")),
        ((4, 5), ("2222", "12223")),
        ((4, 5), ("2222", "22222")),
        ((4, 5), ("2223", "12222")),
    }
    actual77 = {
        (r["n"], r["a"], r["k"], tuple(r["shape"]))
        for r in rows if r["c"] == 77
    }
    actual78 = {
        (r["n"], tuple(r["shape"])) for r in rows if r["c"] == 78
    }
    require(actual77 == expected77, "cut77 list mismatch")
    require(actual78 == expected78, "cut78 list mismatch")
    bound = 1 + Fraction(621 + 610, 2 * 77)
    require(bound == Fraction(1385, 154), "half-mixture arithmetic")
    require(9 - bound == Fraction(1, 154), "strict margin arithmetic")
    return {
        "scope": "Exact enumeration of necessary normalized integer cost "
                 "constraints only; no actual-source realization, support "
                 "argument, or Lean verification.",
        "rows": rows, "cut77_count": len(actual77),
        "cut78_count": len(actual78), "half_mixture_bound": str(bound),
        "strict_margin": str(9 - bound),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = inventory()
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output is not None:
        args.output.write_text(rendered, encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items() if key != "rows"}))


if __name__ == "__main__":
    main()
