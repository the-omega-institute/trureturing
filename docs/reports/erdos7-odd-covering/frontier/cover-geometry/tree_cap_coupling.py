#!/usr/bin/env python3
"""Exact finite-tree row/prefix coupling and original-label height controls.

The reusable interface couple_tree_caps(m, q, radix, depth, source, caps)
uses lowest-digit-first canonical radix trees. Source points are (row, leaf)
integer pairs. Explicit proper-prefix caps have keys (length, residue) and
integer or Fraction values. It returns one exact supported law and metadata.

The ordinary cut proof is separate; these standard-library controls are not
Lean certification. The 540-point consumer imports the existing report442
fixture through --fixture-script, rather than storing another source copy.
"""

from collections import defaultdict, deque
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
from pathlib import Path
import argparse
import json
import runpy


def require(condition, message):
    if not condition:
        raise ValueError(message)


def projected_capacity(radix, depth, leaves, caps):
    """Maximum mass with the pure tree caps, including root capacity one."""
    level = {y: caps[(depth, y)] if y in leaves else F()
             for y in range(radix**depth)}
    for b in range(depth - 1, -1, -1):
        level = {c: min(F(1) if b == 0 else caps[(b, c)],
                        sum((level[c + digit*radix**b] for digit in range(radix)), F()))
                 for c in range(radix**b)}
    return level[0]


def _unit_flow(edge_records, start, finish, denominator):
    """Deterministic integral augmentations, stopped at the requested unit."""
    graph = defaultdict(dict)
    initial = {}
    for u, v, capacity in edge_records:
        amount = capacity * denominator
        require(amount.denominator == 1 and amount >= 0, "integral network scaling")
        require((u, v) not in initial and (v, u) not in initial, "unique directed network edge")
        initial[(u, v)] = amount.numerator
        graph[u][v] = amount.numerator
        graph[v][u] = 0
    value = 0
    augmentations = 0
    while value < denominator:
        previous = {start: None}
        queue = deque([start])
        while queue and finish not in previous:
            u = queue.popleft()
            for v, capacity in graph[u].items():
                if capacity > 0 and v not in previous:
                    previous[v] = u
                    queue.append(v)
        require(finish in previous, "verified premise did not produce the promised unit flow")
        amount = denominator - value
        v = finish
        while previous[v] is not None:
            u = previous[v]
            amount = min(amount, graph[u][v])
            v = u
        v = finish
        while previous[v] is not None:
            u = previous[v]
            graph[u][v] -= amount
            graph[v][u] += amount
            v = u
        value += amount
        augmentations += 1
    flow = {(u, v): F(capacity-graph[u][v], denominator)
            for (u, v), capacity in initial.items()}
    balance = defaultdict(F)
    for (u, v), amount in flow.items():
        require(0 <= amount <= F(initial[(u, v)], denominator), "edge flow respects capacity")
        balance[u] -= amount
        balance[v] += amount
    require(balance[start] == -1 and balance[finish] == 1, "unit source/sink balance")
    require(all(amount == 0 for node, amount in balance.items() if node not in (start, finish)),
            "internal exact flow conservation")
    return flow, augmentations


def couple_tree_caps(m, q, radix, depth, source, caps):
    """Return (law, metadata); reject malformed input or an unsupported premise.

    law maps actual (row, leaf) pairs to positive Fractions. Every q-row
    projected capacity is checked before the private/public network is built.
    All output row, pure-prefix and joint-prefix caps are then recomputed from
    that same literal law. No numerical optimizer is used.
    """
    require(type(m) is int and type(q) is int and 1 <= q <= m, "1 <= q <= m")
    require(type(radix) is int and radix >= 2 and type(depth) is int and depth >= 1,
            "canonical radix>=2 and positive finite depth")
    require(isinstance(caps, dict), "explicit prefix-cap dictionary")
    expected = {(b, c) for b in range(1, depth+1) for c in range(radix**b)}
    require(set(caps) == expected and all(type(b) is int and type(c) is int for b, c in caps),
            "exact proper-prefix cap domain")
    require(all(type(cap) in (int, F) and cap >= 0 for cap in caps.values()),
            "exact nonnegative integer/Fraction caps")
    caps = {key: F(value) for key, value in caps.items()}
    values = list(source)
    require(all(type(p) in (tuple, list) and len(p) == 2 and all(type(z) is int for z in p)
                for p in values), "literal integer source pairs")
    values = [tuple(p) for p in values]
    require(values and len(values) == len(set(values)), "nonempty distinct actual source")
    require(all(0 <= r < m and 0 <= y < radix**depth for r, y in values),
            "source rows and leaves are in the declared carrier")
    points = sorted(values)
    subset_checks = 0
    for selected in combinations(range(m), q):
        leaves = {y for r, y in points if r in selected}
        require(projected_capacity(radix, depth, leaves, caps) == 1,
                f"q-row projection has capacity below one: {selected}")
        subset_checks += 1

    start, finish = ("source",), ("public", 0, 0)
    edges = []
    for r in range(m):
        edges.append((start, ("private", r, 0, 0), F(1, m-q+1)))
        for b, c in sorted(expected):
            edges.append((("private", r, b-1, c % radix**(b-1)),
                          ("private", r, b, c), F(q, m)*caps[(b, c)]))
    for b, c in sorted(expected):
        edges.append((("public", b, c), ("public", b-1, c % radix**(b-1)), caps[(b, c)]))
    for r, y in points:
        edges.append((("private", r, depth, y), ("public", depth, y), F(1)))
    denominator = lcm(*(capacity.denominator for _, _, capacity in edges))
    flow, augmentations = _unit_flow(edges, start, finish, denominator)
    law = {(r, y): flow[(("private", r, depth, y), ("public", depth, y))] for r, y in points}
    law = {point: mass for point, mass in law.items() if mass > 0}
    require(set(law) <= set(points) and sum(law.values(), F()) == 1, "one actual supported probability")
    rows = {r: sum((mass for (rr, y), mass in law.items() if rr == r), F()) for r in range(m)}
    require(all(mass <= F(1, m-q+1) for mass in rows.values()), "same-law row caps")
    pure, joint = {}, {}
    for b, c in sorted(expected):
        pure[(b, c)] = sum((mass for (r, y), mass in law.items() if y % radix**b == c), F())
        require(pure[(b, c)] <= caps[(b, c)], "same-law pure prefix cap")
        for r in range(m):
            joint[(r, b, c)] = sum((mass for (rr, y), mass in law.items()
                                    if rr == r and y % radix**b == c), F())
            require(joint[(r, b, c)] <= F(q, m)*caps[(b, c)], "same-law joint prefix cap")
    return law, {"source_points": len(points), "selected_points": len(law),
                 "q_subset_checks": subset_checks, "network_edges": len(edges),
                 "flow_denominator": denominator, "augmentations": augmentations,
                 "row_masses": [str(rows[r]) for r in range(m)],
                 "pure_prefix_checks": len(pure), "joint_prefix_checks": len(joint)}


def _law_rows(law):
    return [{"row": r, "leaf": y, "mass": str(mass)} for (r, y), mass in sorted(law.items())]


def diagonal_sharpness_control():
    m, q, radix = 5, 3, 7
    caps = {(1, c): F(1, q) for c in range(radix)}
    law, info = couple_tree_caps(m, q, radix, 1, [(r, r) for r in range(m)], caps)
    require(all(law[(r, r)] == F(1, m) for r in range(m)), "diagonal forces uniform1/m")
    require(max(law.values())/caps[(1, 0)] == F(q, m), "sharp joint coefficient")
    return {**info, "law": _law_rows(law), "joint_coefficient_exact": "3/5",
            "scope": "The m-point diagonal argument proves q/m sharpness generally."}


def height_controls():
    def series(h):
        return sum((F(2*j+1, 3**j) for j in range(h+1)), F())
    checks = 0
    for h in range(1, 31):
        sh = series(h)
        require(sh == 3-F(h+2, 3**h), "exact finite geometric sum")
        limit = 3*sh+F(8*(2*h+1), 5*3**h)
        require(limit == 9+F(h-22, 5*3**h), "all-seven-height bound formula")
        for k in range(1, 31):
            sk = series(k)
            bound = sh*sk+F(4*(2*h+1), 5*3**h)*(sk-1)
            literal = sum((F((2*a+1)*(2*b+1), 3**(a+b))
                           *(F(9, 5) if a == h and b > 0 else 1)
                           for a, b in product(range(h+1), range(k+1))), F())
            require(bound == literal < limit, "finite LCM sum and strict truncation")
            if h <= 22:
                require(bound < 9, "finite height range throughH22")
            if h <= 21:
                require(limit < 9, "uniform positive gap throughH21")
            checks += 1
    h3k2 = series(3)*series(2)+F(28, 135)*(series(2)-1)
    require(h3k2 == F(3044, 405), "twelve-label consumer constant")
    require(9+F(3-22, 5*3**3) == F(1196, 135), "H3 all-K constant")
    require(9+F(2-22, 5*3**2) == F(77, 9), "H2 all-K constant")
    return {"finite_height_controls": checks, "H3K2_bound": str(h3k2),
            "H3_all_K_bound": "1196/135", "H2_all_K_bound": "77/9",
            "uniform_gap_range": "1<=H<=21", "finite_strict_range": "1<=H<=22",
            "H22_limit": "9",
            "scope": "All-height results use the ordinary formula proof, not finite enumeration."}


def actual_540_consumer(fixture_script):
    fixture = runpy.run_path(str(fixture_script))
    source = fixture["empty_good_fibre_countercontrol"]()["actual_residues"]
    actual = set(source)
    require(len(source) == len(actual) == 540, "reuse the existing540-point fixture")
    fibres = defaultdict(set)
    for x in source:
        fibres[x % 25].add(((x % 125)//25, x % 49))
    require(len(fibres) == 9, "nine occupied mod25 prefixes")
    require(len({s % 5 for s in fibres}) == 3
            and all(sum(s % 5 == r for s in fibres) == 3 for r in {s % 5 for s in fibres}),
            "actual ternary first-two-five-digit skeleton")
    caps = {(b, c): F(1, 3**b) for b in (1, 2) for c in range(7**b)}
    law, local_records = {}, []
    for s, points in sorted(fibres.items()):
        conditional, info = couple_tree_caps(5, 3, 7, 2, sorted(points), caps)
        for (u, y), mass in conditional.items():
            x = fixture["fine_crt"](s+25*u, y)
            require(x in actual and x % 25 == s and x not in law, "actual fine bridge lift")
            law[x] = mass/9
        local_records.append({"mod25_prefix": s, **info, "conditional_law": _law_rows(conditional)})
    require(sum(law.values(), F()) == 1 and set(law) <= actual, "one lifted actual law")
    require(all(sum(mass for x, mass in law.items() if x % 25 == s) == F(1, 9) for s in fibres),
            "uniform actual mod25 marginal")
    labels = tuple(sorted(5**a*7**b for a, b in product(range(4), range(3))))
    theorem_caps = {5**a*7**b: F(1, 3**(a+b))*(F(9, 5) if a == 3 and b > 0 else 1)
                    for a, b in product(range(4), range(3))}
    maxima = {d: fixture["cylinder_max"](law, d) for d in labels}
    require(all(maxima[d] <= theorem_caps[d] for d in labels), "all twelve same-law cylinder caps")
    upper = sum((maxima[lcm(d, e)] for d, e in product(labels, repeat=2)), F())
    bound = sum((theorem_caps[lcm(d, e)] for d, e in product(labels, repeat=2)), F())
    grouped = sum((F((2*a+1)*(2*b+1))*theorem_caps[5**a*7**b]
                   for a, b in product(range(4), range(3))), F())
    require(bound == grouped == F(3044, 405) and upper <= bound < 9,
            "all144 independently phased ordered-pair bound")
    centered = max(fixture["centered_moment"](law, labels, x) for x in law)
    require(centered <= upper, "literal centered layouts versus all-phase LCM upper")
    return {"source_points": len(source), "selected_actual_points": len(law),
            "selected_actual_law": [{"residue": x, "mass": str(mass)} for x, mass in sorted(law.items())],
            "local_laws": local_records, "original_labels": labels, "ordered_pairs": len(labels)**2,
            "cylinder_maxima": {str(d): str(maxima[d]) for d in labels},
            "theorem_caps": {str(d): str(theorem_caps[d]) for d in labels},
            "actual_LCM_upper": str(upper), "theorem_Gamma_upper": str(bound),
            "centered_layout_lower": str(centered),
            "scope": "One law on the reused actual source; upper bounds keep all12 independently phased labels. No odd-cover realization is claimed."}


def input_controls():
    caps = {(1, 0): F(2, 3), (1, 1): F(1, 2),
            (2, 0): F(1, 3), (2, 1): F(1, 4), (2, 2): F(1, 3), (2, 3): F(1, 4)}
    source = list(product(range(3), range(4)))
    law, info = couple_tree_caps(3, 2, 2, 2, source, caps)
    require(sum(law.values(), F()) == 1, "nonuniform rational-cap consumer")
    rejected = []
    bad_caps = dict(caps)
    bad_caps[(1, 0)] = 0.5
    incomplete = dict(caps)
    del incomplete[(2, 3)]
    cases = [("inexact cap", source, bad_caps),
             ("incomplete cap domain", source, incomplete),
             ("duplicate source point", source+[source[0]], caps),
             ("outside carrier", source+[(3, 0)], caps),
             ("insufficient projected capacity", [(0, 0)], caps)]
    for name, points, capacities in cases:
        try:
            couple_tree_caps(3, 2, 2, 2, points, capacities)
        except ValueError:
            rejected.append(name)
        else:
            raise ValueError(f"failed to reject {name}")
    return {"nonuniform_capacity_control": {**info, "law": _law_rows(law)},
            "rejected_inputs": rejected}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture-script", type=Path,
                        default=Path(__file__).with_name("minimum_source_fibre_lift.py"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    require(args.fixture_script.is_file(), "existing report442 fixture script is required")
    result = {"diagonal_sharpness": diagonal_sharpness_control(),
              "height_bounds": height_controls(), "input_controls": input_controls(),
              "actual_540_consumer": actual_540_consumer(args.fixture_script),
              "scope": "Ordinary finite-flow proof with exact standard-library constructors and controls; no Lean certification."}
    payload = json.dumps(result, indent=2)+"\n"
    if args.output:
        args.output.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
