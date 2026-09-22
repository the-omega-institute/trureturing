#!/usr/bin/env python3
"""Exact layout-mixture and tree-rank certificates at 5-height one.

The carrier is {1,2,3,4} x Z/7^K. A layout gives an independent literal
residue for every divisor in (1,5,7,35,...,7^K,5*7^K). Residues selecting
the absent row zero are allowed. No compatibility of phases is imposed.

This module computes exact finite certificates. It does not prove a new
source theorem or an unrestricted covering conclusion. Runtime and output
size grow with the explicitly evaluated carrier, of size 4*7^K.

With no arguments, run exact controls. With a JSON path, read:
  {"height": 1,
   "layouts": [{"weight": "1/2", "phases": [0,1,0,6]},
               {"weight": "1/2", "phases": [0,2,1,2]}],
   "target": "2"}
The optional target defaults to 2*(3-(K+2)/3^K). JSON weights/targets are
integers or exact rational strings, never floating-point numbers.
"""
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import argparse
import json

F = Fraction
ROWS = (1, 2, 3, 4)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def exact(value, name):
    require(type(value) in (int, F), name + " must be an integer or Fraction")
    return F(value)


def original_divisors(height):
    """Original label order, including the divisor-one label."""
    require(type(height) is int and height >= 0, "height must be a nonnegative integer")
    return tuple(d for j in range(height + 1) for d in (7 ** j, 5 * 7 ** j))


def validate_layout(height, phases):
    divisors = original_divisors(height)
    require(isinstance(phases, (tuple, list)) and len(phases) == len(divisors),
            "one phase is required for every original divisor")
    require(all(type(a) is int and 0 <= a < d for a, d in zip(phases, divisors)),
            "each phase must be a literal integer residue at its divisor")
    return tuple(phases)


def _cost(divisors, phases, row, residue):
    count = 0
    for d, a in zip(divisors, phases):
        if d % 5 == 0:
            q = d // 5
            count += int(row == a % 5 and residue % q == a % q)
        else:
            count += int(residue % d == a)
    return count * count


def literal_layout_cost(height, phases, point):
    """Evaluate the literal complete squared load at one carrier point."""
    divisors = original_divisors(height)
    phases = validate_layout(height, phases)
    require(isinstance(point, (tuple, list)) and len(point) == 2, "point must be a pair")
    row, residue = point
    require(type(row) is int and row in ROWS and type(residue) is int
            and 0 <= residue < 7 ** height, "point outside the four-row carrier")
    return _cost(divisors, phases, row, residue)


def evaluate_layout_mixture(height, components):
    """Return the exact cost on every carrier point.

    Each component is (weight, phases); weights must be nonnegative exact
    integers/Fractions summing to one. Zero-weight legal layouts are allowed.
    """
    divisors = original_divisors(height)
    checked = []
    for component in components:
        require(isinstance(component, (tuple, list)) and len(component) == 2,
                "component must be (weight, phases)")
        weight, phases = component
        weight = exact(weight, "weight")
        require(weight >= 0, "weight must be nonnegative")
        checked.append((weight, validate_layout(height, phases)))
    require(checked and sum((w for w, _ in checked), F(0)) == 1,
            "mixture weights must sum to one")
    return {(r, y): sum((w * _cost(divisors, p, r, y) for w, p in checked), F(0))
            for r, y in product(ROWS, range(7 ** height))}


def bary_tree_witness(values, height, branching):
    """Maximize the least leaf value over complete b-ary low-digit-prefix trees.

    values is a complete residue-to-exact-value dictionary on Z/7^height.
    Return the exact bottleneck and the leaves of one attaining tree.
    """
    original_divisors(height)
    require(type(branching) is int and 1 <= branching <= 7, "branching must be in 1..7")
    require(isinstance(values, dict), "tree values must be a dictionary")
    require(all(type(y) is int for y in values)
            and set(values) == set(range(7 ** height)), "tree values need every literal residue")
    checked = {y: exact(v, "leaf value") for y, v in values.items()}

    def visit(depth, table):
        if depth == 0:
            return table[0], (0,)
        children = []
        for digit in range(7):
            value, leaves = visit(depth - 1, {y // 7: v for y, v in table.items() if y % 7 == digit})
            children.append((value, digit, leaves))
        children.sort(key=lambda item: (-item[0], item[1]))
        selected = children[:branching]
        leaves = tuple(sorted(digit + 7 * y for _, digit, tree in selected for y in tree))
        return min(v for v, _, _ in selected), leaves

    value, leaves = visit(height, checked)
    return {"value": value, "leaves": leaves}


def contains_bary_tree(leaves, height, branching):
    """Independent Boolean tree test by contracting complete child sets."""
    original_divisors(height)
    require(type(branching) is int and 1 <= branching <= 7, "branching must be in 1..7")
    leaves = set(leaves)
    require(all(type(y) is int and 0 <= y < 7 ** height for y in leaves),
            "tree leaf outside residue space")
    good = leaves
    for depth in range(height, 0, -1):
        modulus = 7 ** (depth - 1)
        parents = {y % modulus for y in good}
        good = {p for p in parents
                if sum(p + modulus * digit in good for digit in range(7)) >= branching}
    return 0 in good


def row_tree_witness(costs, height, rows, branching):
    """Take a row maximum at each leaf, then supply a complete tree and row witnesses."""
    original_divisors(height)
    require(isinstance(rows, (tuple, list)) and rows and len(set(rows)) == len(rows)
            and all(type(r) is int and r in ROWS for r in rows), "distinct allowed rows required")
    require(isinstance(costs, dict)
            and set(costs) == set(product(ROWS, range(7 ** height))), "complete carrier cost required")
    require(all(type(r) is int and type(y) is int for r, y in costs), "literal point keys required")
    checked = {p: exact(v, "point cost") for p, v in costs.items()}
    chosen = {y: min(rows, key=lambda r: (-checked[r, y], r)) for y in range(7 ** height)}
    tree = bary_tree_witness({y: checked[chosen[y], y] for y in chosen}, height, branching)
    points = tuple((chosen[y], y) for y in tree["leaves"])
    return {"rows": tuple(rows), "branching": branching, "value": tree["value"],
            "leaves": tree["leaves"], "points": points}


def default_target(height):
    original_divisors(height)
    return 2 * (3 - F(height + 2, 3 ** height))


def audit_layout_mixture(height, components, target=None):
    """Compute B, optional four-active-row rank B4, and exact constructive certificates.

    strict_target_verified means that the literal strict highset passes all
    six pair-ternary and full-fiveary tests. It is a counterexample to the
    default comparison only when target is the default 2*t_height.
    """
    threshold = default_target(height) if target is None else exact(target, "target")
    costs = evaluate_layout_mixture(height, components)
    groups = [(pair, 3) for pair in combinations(ROWS, 2)] + [(ROWS, 5)]
    witnesses = tuple(row_tree_witness(costs, height, rows, b) for rows, b in groups)
    rank = min(w["value"] for w in witnesses)
    source = set().union(*(set(w["points"]) for w in witnesses))
    require(all(costs[p] >= rank for p in source), "constructive rank lower certificate")
    for rows, b in groups:
        require(contains_bary_tree({y for r, y in source if r in rows}, height, b),
                "witness source must pass every tree test")
    row_points = {r: min(range(7 ** height), key=lambda y: (-costs[r, y], y)) for r in ROWS}
    row_maxima = {r: costs[r, row_points[r]] for r in ROWS}
    four_rank = min(rank, min(row_maxima.values()))
    four_source = source | {(r, y) for r, y in row_points.items()}
    require({r for r, _ in four_source} == set(ROWS)
            and all(costs[p] >= four_rank for p in four_source), "four-row witness certificate")
    strict = {p for p, v in costs.items() if v > threshold}
    strict_tests = all(contains_bary_tree({y for r, y in strict if r in rows}, height, b)
                       for rows, b in groups)
    require(strict_tests == (rank > threshold), "strict highset/rank agreement")
    strict_four = strict_tests and {r for r, _ in strict} == set(ROWS)
    require(strict_four == (four_rank > threshold), "strict four-row highset/rank agreement")
    return {"height": height, "divisors": original_divisors(height), "target": threshold,
            "default_target": default_target(height), "rank": rank, "four_active_rank": four_rank,
            "row_maxima": row_maxima, "witnesses": witnesses, "witness_source": tuple(sorted(source)),
            "four_active_witness_source": tuple(sorted(four_source)), "strict_highset": tuple(sorted(strict)),
            "strict_target_verified": strict_tests, "strict_four_active_verified": strict_four,
            "default_comparison_counterexample": strict_tests and threshold == default_target(height),
            "costs": costs}


def _aligned_layout(height, row, residue):
    modulus = 7 ** height
    x = residue + modulus * (((row - residue) * pow(modulus, -1, 5)) % 5)
    return tuple(x % d for d in original_divisors(height))


def self_check():
    require(original_divisors(2) == (1, 5, 7, 35, 49, 245), "literal original label order")
    require(literal_layout_cost(1, (0, 1, 0, 6), (1, 0)) == 9
            and literal_layout_cost(1, (0, 1, 0, 6), (1, 6)) == 9,
            "independent incompatible phases remain literal")
    zero = audit_layout_mixture(2, [(1, (0, 0, 0, 0, 0, 0))])
    require(zero["rank"] == 1 and not zero["strict_target_verified"], "absent-row phase control")
    require(zero["costs"][1, 0] == 9 and zero["costs"][1, 1] == 1,
            "row-zero events vanish, pure 7-events remain")

    # An actual failure of convexity within the original literal layout class.
    layouts = [_aligned_layout(1, r, c) for r, c in product(ROWS, range(7))]
    deterministic_ranks = [audit_layout_mixture(1, [(1, p)])["rank"] for p in layouts]
    require(deterministic_ranks == [F(1)] * 28, "aligned deterministic ranks")
    mixture = [(F(1, 28), p) for p in layouts]
    averaged = audit_layout_mixture(1, mixture)
    require(set(averaged["costs"].values()) == {F(5, 2)}
            and averaged["rank"] == averaged["four_active_rank"] == F(5, 2),
            "literal-mixture nonconvexity control")
    strict = audit_layout_mixture(1, mixture, F(2))
    boundary = audit_layout_mixture(1, mixture, F(5, 2))
    require(strict["strict_target_verified"] and strict["strict_four_active_verified"]
            and not strict["default_comparison_counterexample"], "custom-threshold positive certificate")
    require(not boundary["strict_target_verified"] and not boundary["strict_highset"],
            "strict versus non-strict threshold boundary")

    three_rows = [(F(1, 21), _aligned_layout(1, r, c))
                  for r, c in product((2, 3, 4), range(7))]
    three = audit_layout_mixture(1, three_rows, F(2))
    require(all(three["costs"][1, y] == F(10, 7) for y in range(7))
            and all(three["costs"][r, y] == F(20, 7)
                    for r, y in product((2, 3, 4), range(7))),
            "literal three-row mixture costs")
    require(three["rank"] == F(20, 7) and three["four_active_rank"] == F(10, 7)
            and three["strict_target_verified"] and not three["strict_four_active_verified"]
            and {r for r, _ in three["strict_highset"]} == {2, 3, 4},
            "B and B4 distinguish actual active-row requirements")

    selected = {c + 7 * ((c + j) % 7) for c in (0, 3, 6) for j in range(3)}
    table = {y: F(int(y in selected)) for y in range(49)}
    ternary = bary_tree_witness(table, 2, 3)
    require(ternary["value"] == 1 and set(ternary["leaves"]) == selected
            and contains_bary_tree(selected, 2, 3), "prefix-dependent constructive tree")
    require(bary_tree_witness(table, 2, 5)["value"] == 0
            and not contains_bary_tree(selected, 2, 5), "different branching thresholds")
    base = audit_layout_mixture(0, [(F(1, 4), (0, r)) for r in ROWS])
    require(base["rank"] == F(7, 4), "height-zero boundary")

    invalid = (
        lambda: original_divisors(True),
        lambda: original_divisors(-1),
        lambda: evaluate_layout_mixture(1, [(1.0, layouts[0])]),
        lambda: evaluate_layout_mixture(1, [(True, layouts[0])]),
        lambda: evaluate_layout_mixture(1, [(F(-1), layouts[0]), (2, layouts[1])]),
        lambda: evaluate_layout_mixture(1, [(F(1, 2), layouts[0])]),
        lambda: validate_layout(1, (0, 1, 2)),
        lambda: validate_layout(1, (0, 5, 0, 0)),
        lambda: validate_layout(1, (0, 1.0, 0, 0)),
        lambda: validate_layout(1, (0, True, 0, 0)),
        lambda: audit_layout_mixture(1, mixture, 2.0),
        lambda: bary_tree_witness({0: F(1)}, 1, 3),
        lambda: bary_tree_witness({0: F(1)}, 0, 8),
        lambda: contains_bary_tree([49], 2, 3),
    )
    rejected = 0
    for operation in invalid:
        try:
            operation()
        except ValueError:
            rejected += 1
    require(rejected == len(invalid), "invalid exact-input controls")
    return {"literal_aligned_layouts": 28, "each_deterministic_rank": "1",
            "mixture_rank": "5/2", "constant_mixture_cost": "5/2",
            "three_row_mixture_rank": "20/7", "three_row_mixture_four_active_rank": "10/7",
            "custom_threshold_certificate": True, "default_counterexample": False,
            "prefix_dependent_tree_leaves": len(selected), "invalid_controls": rejected,
            "scope": "exact finite controls, including nonconvexity of the literal-layout rank functional"}


def _json_exact(value, name):
    if type(value) is int:
        return F(value)
    require(type(value) is str, name + " must be an integer or exact rational string")
    try:
        return F(value)
    except (ValueError, ZeroDivisionError) as error:
        raise ValueError(name + " is not a valid exact rational") from error


def _jsonable(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {str(k): _jsonable(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [_jsonable(v) for v in value]
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", help="exact JSON certificate; omit to run controls")
    parser.add_argument("--include-costs", action="store_true", help="include the complete carrier cost table")
    args = parser.parse_args()
    if args.input is None:
        print(json.dumps(self_check(), indent=2))
        return
    payload = json.loads(Path(args.input).read_text())
    require(isinstance(payload, dict) and set(payload) <= {"height", "layouts", "target"}
            and {"height", "layouts"} <= set(payload), "JSON certificate fields")
    require(isinstance(payload["layouts"], list), "JSON layouts must be a list")
    components = []
    for item in payload["layouts"]:
        require(isinstance(item, dict) and set(item) == {"weight", "phases"}, "JSON layout fields")
        components.append((_json_exact(item["weight"], "weight"), item["phases"]))
    target = _json_exact(payload["target"], "target") if "target" in payload else None
    result = audit_layout_mixture(payload["height"], components, target)
    costs = result.pop("costs")
    if args.include_costs:
        result["costs"] = [{"row": r, "residue": y, "value": v} for (r, y), v in sorted(costs.items())]
    print(json.dumps(_jsonable(result), indent=2))


if __name__ == "__main__":
    main()
