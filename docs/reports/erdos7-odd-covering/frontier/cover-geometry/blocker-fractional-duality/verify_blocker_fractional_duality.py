#!/usr/bin/env python3
"""Exact finite LP audit for the Section 243 blocker family.

For each label, an option is an activation set T(i,b).  Inclusion-minimal
blockers are the sets meeting every option.  The verifier computes, using
only rational Gaussian elimination, both sides of the finite LP pair

    min sum_v w_v x_v       max sum_(i,R) alpha_(i,R)
    sum_{v in R} x_v >= 1   sum_(i,R:v in R) alpha_(i,R) <= w_v
    x_v >= 0                alpha_(i,R) >= 0.

The integral Section 243 value is checked separately by enumerating U subset V.
The result is a finite exact audit.  It does not produce a whole-cover
replacement, and it does not close the unrestricted lower-bound bridge.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path
from typing import Iterable, Sequence


DEFAULT_OUTPUT = Path(__file__).with_suffix(".json")


def subsets(n: int) -> range:
    return range(1 << n)


def mask_elements(mask: int, n: int) -> list[int]:
    return [v for v in range(n) if mask & (1 << v)]


def minimal_blockers(options: Sequence[int], n: int) -> tuple[int, ...]:
    candidates = tuple(
        r for r in subsets(n) if all(r & option for option in options)
    )
    candidate_set = set(candidates)
    return tuple(
        r
        for r in candidates
        if all(not (s != r and (s & r) == s) for s in candidate_set)
    )


def option_catalogue(n: int, max_options: int) -> tuple[tuple[int, ...], ...]:
    options = tuple(subsets(n))
    return tuple(
        choice
        for count in range(1, max_options + 1)
        for choice in itertools.combinations(options, count)
    )


def solve_square(matrix: Sequence[Sequence[Fraction]], rhs: Sequence[Fraction]) -> tuple[Fraction, ...] | None:
    """Return the unique solution, or None for a singular square system."""

    n = len(rhs)
    if len(matrix) != n or any(len(row) != n for row in matrix):
        raise ValueError("non-square system")
    augmented = [list(row) + [rhs[i]] for i, row in enumerate(matrix)]
    for col in range(n):
        pivot = next((row for row in range(col, n) if augmented[row][col]), None)
        if pivot is None:
            return None
        augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
        scale = augmented[col][col]
        augmented[col] = [entry / scale for entry in augmented[col]]
        for row in range(n):
            if row == col or not augmented[row][col]:
                continue
            scale = augmented[row][col]
            augmented[row] = [
                augmented[row][j] - scale * augmented[col][j]
                for j in range(n + 1)
            ]
    return tuple(augmented[row][-1] for row in range(n))


def primal_fractional(blockers: Sequence[int], weights: Sequence[int], n: int) -> Fraction:
    """Exact vertex enumeration for the bounded optimum of the primal LP."""

    if n == 0:
        return Fraction(0)
    rows: list[tuple[tuple[Fraction, ...], Fraction]] = []
    for blocker in blockers:
        rows.append(
            (tuple(Fraction(1 if blocker & (1 << v) else 0) for v in range(n)), Fraction(1))
        )
    for v in range(n):
        rows.append(
            (tuple(Fraction(1 if u == v else 0) for u in range(n)), Fraction(0))
        )
    best: Fraction | None = None
    for indices in itertools.combinations(range(len(rows)), n):
        matrix = [rows[i][0] for i in indices]
        rhs = [rows[i][1] for i in indices]
        point = solve_square(matrix, rhs)
        if point is None or any(value < 0 for value in point):
            continue
        if any(sum(point[v] for v in range(n) if blocker & (1 << v)) < 1 for blocker in blockers):
            continue
        value = sum(Fraction(weights[v]) * point[v] for v in range(n))
        if best is None or value < best:
            best = value
    if best is None:
        raise AssertionError("feasible blocker cover has no enumerated vertex")
    return best


def dual_fractional(blockers: Sequence[int], weights: Sequence[int], n: int) -> Fraction:
    """Exact vertex enumeration for the packing dual."""

    dimension = len(blockers)
    if dimension == 0:
        return Fraction(0)
    rows: list[tuple[tuple[Fraction, ...], Fraction]] = []
    for v in range(n):
        rows.append(
            (
                tuple(Fraction(1 if blocker & (1 << v) else 0) for blocker in blockers),
                Fraction(weights[v]),
            )
        )
    for j in range(dimension):
        rows.append(
            (tuple(Fraction(1 if k == j else 0) for k in range(dimension)), Fraction(0))
        )
    best: Fraction | None = None
    for indices in itertools.combinations(range(len(rows)), dimension):
        matrix = [rows[i][0] for i in indices]
        rhs = [rows[i][1] for i in indices]
        point = solve_square(matrix, rhs)
        if point is None or any(value < 0 for value in point):
            continue
        if any(
            sum(point[j] for j, blocker in enumerate(blockers) if blocker & (1 << v))
            > weights[v]
            for v in range(n)
        ):
            continue
        value = sum(point)
        if best is None or value > best:
            best = value
    if best is None:
        raise AssertionError("dual feasible region has no enumerated vertex")
    return best


def integral_value(option_families: Sequence[Sequence[int]], weights: Sequence[int], n: int) -> int:
    feasible = (
        u
        for u in subsets(n)
        if all(any((option & ~u) == 0 for option in options) for options in option_families)
    )
    return min(sum(weights[v] for v in range(n) if u & (1 << v)) for u in feasible)


def blocker_value(option_families: Sequence[Sequence[int]], weights: Sequence[int], n: int) -> tuple[int, Fraction, Fraction, tuple[int, ...]]:
    blockers = tuple(
        blocker
        for options in option_families
        for blocker in minimal_blockers(options, n)
    )
    integral = min(
        sum(weights[v] for v in range(n) if u & (1 << v))
        for u in subsets(n)
        if all(u & blocker for blocker in blockers)
    )
    primal = primal_fractional(blockers, weights, n)
    dual = dual_fractional(blockers, weights, n)
    return integral, primal, dual, blockers


def describe_gap(n: int, options: Sequence[int], weights: Sequence[int]) -> dict[str, object]:
    integral, primal, dual, blockers = blocker_value((options,), weights, n)
    return {
        "universe_size": n,
        "options": [mask_elements(option, n) for option in options],
        "minimal_blockers": [mask_elements(blocker, n) for blocker in blockers],
        "weights": list(weights),
        "integral_lambda": integral,
        "fractional_cover": str(primal),
        "fractional_packing": str(dual),
        "integrality_gap": str(Fraction(integral) / primal),
    }


def audit() -> dict[str, object]:
    failures: list[dict[str, object]] = []
    exact_checks = 0
    strict_gaps: list[dict[str, object]] = []
    summary: list[dict[str, object]] = []

    # Full finite catalogue for n<=3.  This is the same bounded activation
    # family used by the existing blocker-equivalence audit, with one/two
    # labels (and up to three labels for n<=2).
    for n in range(4):
        max_options = (1 << n) if n <= 3 else 2
        catalogue = option_catalogue(n, max_options)
        max_labels = 3 if n <= 2 else 2
        instances = 0
        for label_count in range(1, max_labels + 1):
            for indices in itertools.combinations_with_replacement(range(len(catalogue)), label_count):
                options = tuple(catalogue[index] for index in indices)
                for weights in (tuple(1 for _ in range(n)), tuple(range(1, n + 1))):
                    instances += 1
                    exact_checks += 1
                    integral = integral_value(options, weights, n)
                    blocker_integral, primal, dual, blockers = blocker_value(options, weights, n)
                    if blocker_integral != integral or primal != dual or primal > integral:
                        failures.append({
                            "n": n,
                            "label_indices": list(indices),
                            "weights": list(weights),
                            "integral": integral,
                            "blocker_integral": blocker_integral,
                            "primal": str(primal),
                            "dual": str(dual),
                            "blockers": [mask_elements(blocker, n) for blocker in blockers],
                        })
                    if primal < integral and len(strict_gaps) < 8:
                        strict_gaps.append({
                            "n": n,
                            "label_indices": list(indices),
                            "weights": list(weights),
                            "integral": integral,
                            "fractional": str(primal),
                            "gap": str(Fraction(integral) / primal),
                        })
        summary.append({
            "universe_size": n,
            "catalogue_size": len(catalogue),
            "max_labels": max_labels,
            "instances": instances,
            "weights_per_instance": 2,
        })

    # A deterministic larger representative set checks the same exact solver
    # at n=4,5 without claiming exhaustive coverage of those catalogues.
    representative_checks = 0
    for n, max_options, indices in ((4, 2, (0, 1, -1)), (5, 2, (0, 1, 2, -1))):
        catalogue = option_catalogue(n, max_options)
        selected = tuple(catalogue[index] for index in indices)
        instances = [((family,), tuple(1 for _ in range(n))) for family in selected]
        instances += [
            ((selected[0], selected[-1]), tuple(range(1, n + 1))),
            ((selected[1], selected[-1]), tuple(reversed(range(1, n + 1)))),
        ]
        for options, weights in instances:
            representative_checks += 1
            exact_checks += 1
            integral = integral_value(options, weights, n)
            blocker_integral, primal, dual, blockers = blocker_value(options, weights, n)
            if blocker_integral != integral or primal != dual or primal > integral:
                failures.append({
                    "n": n,
                    "representative": True,
                    "weights": list(weights),
                    "integral": integral,
                    "blocker_integral": blocker_integral,
                    "primal": str(primal),
                    "dual": str(dual),
                    "blockers": [mask_elements(blocker, n) for blocker in blockers],
                })
            if primal < integral and len(strict_gaps) < 8:
                strict_gaps.append({
                    "n": n,
                    "representative": True,
                    "weights": list(weights),
                    "integral": integral,
                    "fractional": str(primal),
                    "gap": str(Fraction(integral) / primal),
                })

    # The triangle options give the first explicit gap: Lambda=2 but the
    # fractional cover/packing value is 3/2.
    triangle = describe_gap(3, (0b011, 0b101, 0b110), (1, 1, 1))
    if triangle["integral_lambda"] != 2 or triangle["fractional_cover"] != "3/2" or triangle["fractional_packing"] != "3/2":
        failures.append({"triangle": triangle})

    return {
        "schema": "section243_blocker_fractional_duality_v1",
        "status": "PASS" if not failures else "FAIL",
        "scope": {
            "exhaustive": "all option families on universes n=0..3, one/two labels (three labels for n<=2), two positive integer weight vectors",
            "representatives": "three one-label and two two-label systems at each of n=4,5",
            "arithmetic": "all LP values and certificates use Fraction and exact Gaussian elimination",
            "meaning": "finite audit of the blocker LP pair; no unrestricted whole-cover or EB1 conclusion",
        },
        "summary": summary,
        "exact_checks": exact_checks,
        "representative_checks": representative_checks,
        "strict_integrality_gaps": strict_gaps,
        "triangle_gap": triangle,
        "failures": failures,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    result = audit()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": result["status"],
        "output": str(args.output),
        "exact_checks": result["exact_checks"],
        "representative_checks": result["representative_checks"],
        "strict_gaps": len(result["strict_integrality_gaps"]),
        "failures": len(result["failures"]),
    }, ensure_ascii=False, sort_keys=True))
    if result["status"] != "PASS":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
