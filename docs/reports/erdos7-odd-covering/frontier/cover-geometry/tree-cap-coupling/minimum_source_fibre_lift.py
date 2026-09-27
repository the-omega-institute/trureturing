#!/usr/bin/env python3
"""Exact constructors for minimum-projection and joint-prefix source lifts.

Uses only Python's standard library. Input, when supplied, is a JSON list
of distinct literal residues modulo6125. The theorem is proved separately;
no exhaustive arbitrary-source or Lean claim is made by these controls.
"""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm
import argparse
import json

COARSE = (1, 5, 7, 25, 35, 175)
FINE = tuple(sorted(5**a * 7**b for a in range(4) for b in range(3)))
TAIL_GROUPS = ((3, 0, 7, F(1, 45)), (3, 1, 21, F(1, 45)),
               (3, 2, 35, F(1, 45)), (0, 2, 5, F(1, 15)),
               (1, 2, 15, F(1, 45)), (2, 2, 25, F(1, 45)))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def fine_crt(x5, y7):
    require(0 <= x5 < 125 and 0 <= y7 < 49, "fine CRT coordinates")
    x = x5 + 125 * ((y7 - x5) * 20 % 49)
    require(0 <= x < 6125 and x % 125 == x5 and x % 49 == y7, "fine CRT")
    return x


def coarse_crt(r, a, y):
    x5 = r + 5 * a
    x = x5 + 25 * ((y - x5) * 2 % 7)
    require(x % 25 == x5 and x % 7 == y, "coarse CRT")
    return x


def coarse_coordinates(s):
    return s % 5, (s % 25) // 5, s % 7


def empty_rectangle(edges):
    for aa in combinations(range(5), 3):
        for dd in combinations(range(7), 5):
            if not any((a, d) in edges for a in aa for d in dd):
                return aa, dd
    return None


def matching(edges):
    neighbors = {a: sorted(b for u, b in edges if u == a) for a in range(5)}
    right_to_left = {}

    def augment(a, seen):
        for b in neighbors[a]:
            if b in seen:
                continue
            seen.add(b)
            if b not in right_to_left or augment(right_to_left[b], seen):
                right_to_left[b] = a
                return True
        return False

    for a in range(5):
        augment(a, set())
    result = sorted((a, b) for b, a in right_to_left.items())
    require(all(e in edges for e in result), "matching support")
    require(len({a for a, b in result}) == len(result), "matching left uniqueness")
    require(len({b for a, b in result}) == len(result), "matching right uniqueness")
    return result


def cylinder_max(law, d):
    counts = defaultdict(F)
    for x, mass in law.items():
        counts[x % d] += mass
    return max(counts.values(), default=F())


def centered_moment(law, labels, center):
    return sum((mass * sum(x % d == center % d for d in labels)**2
                for x, mass in law.items()), F())


def construct(actual_residues):
    values = list(actual_residues)
    require(values and all(type(x) is int and 0 <= x < 6125 for x in values),
            "nonempty literal fine carrier input")
    require(len(values) == len(set(values)), "distinct input source points")
    require(all(x % 5 != 0 for x in values), "missing first-five root zero")
    fibres = defaultdict(set)
    for x in values:
        fibres[x % 175].add(((x % 125) // 25, (x % 49) // 7))
    ss = sorted(fibres)
    require(len(ss) == 15, "minimum coarse cardinality15")
    roots = sorted({s % 5 for s in ss})
    require(len(roots) == 3, "minimum coarse class has three occupied roots")
    for r in roots:
        points = [coarse_coordinates(s) for s in ss if s % 5 == r]
        require(len(points) == 5 and len({a for _, a, _ in points}) == 5
                and len({y for _, _, y in points}) == 5,
                "each occupied root is a five-child/five-column matching")

    absent_roots = sorted(set(range(5)) - set(roots))
    require(len(absent_roots) == 2, "two empty first-five roots")
    selected, fibre_rows, isolations = [], [], []
    for s in ss:
        r, a, y = coarse_coordinates(s)
        peers = sorted(t for t in ss if t % 5 == r and t != s)
        b, c = [coarse_coordinates(t)[1] for t in peers[:2]]
        removed_cols = {coarse_coordinates(t)[2] for t in peers[:2]}
        roots_test = set(absent_roots) | {r}
        cols_test = set(range(7)) - removed_cols
        hits = [t for t in ss if t % 5 in roots_test
                and (t % 5 != r or (t % 25) // 5 in {a, b, c})
                and t % 7 in cols_test]
        require(hits == [s], "literal coarse product tree isolates the target cell")
        rectangle = empty_rectangle(fibres[s])
        require(rectangle is None, f"fine fibre{s} misses rectangle{rectangle}")
        matches = matching(fibres[s])
        require(len(matches) >= 3, "rectangle-blocking fibre has matching size3")
        kept = matches[:3]
        for u, v in kept:
            point = fine_crt(r + 5 * a + 25 * u, y + 7 * v)
            require(point in values and point % 175 == s, "selected actual fine point")
            selected.append(point)
        fibre_rows.append({"coarse_residue": s, "edges": [list(e) for e in sorted(fibres[s])],
                           "maximum_matching_size": len(matches),
                           "selected_matching": [list(e) for e in kept]})
        isolations.append({"coarse_residue": s, "first_five_roots": sorted(roots_test),
                           "second_five_digits": [a, b, c],
                           "seven_roots": sorted(cols_test)})

    require(len(selected) == len(set(selected)) == 45, "45 selected actual residues")
    law = {x: F(1, 45) for x in selected}
    coarse_law = {s: F(1, 15) for s in ss}
    require(all(sum(w for x, w in law.items() if x % 175 == s) == F(1, 15)
                for s in ss), "uniform coarse marginal is preserved")
    coarse_max = {d: cylinder_max(coarse_law, d) for d in COARSE}
    coarse_lcm_upper = sum((coarse_max[lcm(d, e)] for d, e in product(COARSE, repeat=2)), F())
    coarse_center_max = max(centered_moment(coarse_law, COARSE, s) for s in ss)
    require(coarse_lcm_upper == coarse_center_max == F(68, 15), "exact uniform coarse Gamma")

    fine_max = {d: cylinder_max(law, d) for d in FINE}
    pairs = [(d, e) for d, e in product(FINE, repeat=2) if lcm(d, e) not in COARSE]
    require(len(pairs) == 108, "all noncoarse ordered pairs")
    actual_tail_upper = sum((fine_max[lcm(d, e)] for d, e in pairs), F())
    grouped_tail = F()
    for a, b, count, cap in TAIL_GROUPS:
        modulus = 5**a * 7**b
        require(sum(lcm(d, e) == modulus for d, e in pairs) == count, "LCM pair multiplicity")
        require(fine_max[modulus] <= cap, "same-law fine cylinder cap")
        grouped_tail += count * cap
    require(grouped_tail == F(118, 45), "tail coefficient sum")
    require(coarse_lcm_upper + grouped_tail == F(322, 45) < 9, "uniform theorem bound")
    require(actual_tail_upper <= grouped_tail, "exact actual LCM tail improves or equals certificate")
    literal_center_lower = max(centered_moment(law, FINE, x) for x in selected)
    require(literal_center_lower <= coarse_lcm_upper + actual_tail_upper, "literal lower versus all-phase upper")
    return {"source_points": len(values), "coarse_points": ss,
            "source_avoids_seven_root_zero": all(x % 7 != 0 for x in values),
            "occupied_five_roots": roots, "isolations": isolations, "fibres": fibre_rows,
            "selected_actual_residues": sorted(selected), "weight_per_point": "1/45",
            "original_coarse_labels": COARSE, "original_fine_labels": FINE,
            "local_rectangle_checks": 15 * 10 * 21,
            "coarse_cylinder_maxima": {str(d): str(m) for d, m in coarse_max.items()},
            "fine_cylinder_maxima": {str(d): str(m) for d, m in fine_max.items()},
            "coarse_Gamma_exact": str(coarse_lcm_upper),
            "fine_actual_LCM_upper": str(coarse_lcm_upper + actual_tail_upper),
            "fine_uniform_theorem_upper": "322/45",
            "fine_centered_layout_lower": str(literal_center_lower)}


def consumer(nonstandard):
    roots = (1, 2, 4) if nonstandard else (1, 2, 3)
    column_lists = ((1, 4, 2, 5, 3), (6, 3, 5, 2, 4), (4, 1, 6, 2, 5))
    base = ((0, 0), (1, 1), (1, 2), (2, 1), (2, 3), (3, 1), (3, 4))
    result = []
    for j, r in enumerate(roots):
        for a in range(5):
            y = column_lists[j][a] if nonstandard else a + 1
            edges = [(v, u) for u, v in base] if (r + a) % 2 else list(base)
            for u, v in edges:
                if nonstandard:
                    u = (2 * u + r + a + y) % 5
                    v = (3 * v + 2 * r + a + y) % 7
                result.append(fine_crt(r + 5 * a + 25 * u, y + 7 * v))
    require(len(set(result)) == 105, "consumer actual point count")
    return sorted(result)


def empty_good_fibre_countercontrol():
    """An actual CRT source blocking full product trees with no good fibre.

    Full trees are handled by a quantified witness construction. The finite
    loops check every local choice used by that construction, not every pair
    of full trees. This source is not claimed to arise from an odd cover.
    """
    roots = {1, 2, 3}
    children = {0, 1, 2}
    columns = set(range(1, 7))
    tails7 = set(range(5))

    def tails5(y):
        return {0, 1} if y <= 3 else {1, 2}

    points = sorted(fine_crt(r + 5*a + 25*u, y + 7*v)
                    for r, a, y, v in product(roots, children, columns, tails7)
                    for u in tails5(y))
    actual = set(points)
    require(len(points) == len(actual) == 540, "540 distinct actual CRT points")
    require(all(x % 5 != 0 and x % 7 != 0 and x % 5 != 4 for x in actual),
            "missing first-five roots0,4 and first-seven root0")
    fibres = defaultdict(set)
    for x in points:
        fibres[x % 175].add(((x % 125)//25, (x % 49)//7))
    require(len(fibres) == 54, "54 occupied coarse cells")
    for s, edges in fibres.items():
        r, a, y = coarse_coordinates(s)
        require(r in roots and a in children and y in columns, "coarse support")
        require(edges == set(product(tails5(y), tails7)), "exact2-by5 fibre")
        require(len(matching(edges)) == 2, "every actual fibre has matching number2")
    good = [s for s, edges in fibres.items() if len(matching(edges)) >= 3]
    require(not good, "good-fibre coarse source is empty")
    for r in roots:
        edges = {(a, y) for s in fibres for rr, a, y in [coarse_coordinates(s)] if rr == r}
        require(edges == set(product(children, columns)), "each coarse root is3-by6")
        require(empty_rectangle(edges) is None, "three robust coarse roots")

    triples5 = [set(t) for t in combinations(range(5), 3)]
    fives7 = [set(t) for t in combinations(range(7), 5)]
    # These are all local assertions in the full-tree witness construction.
    require(all(t & roots and t & children for t in triples5),
            "any ternary root/second-child choice intersects the source")
    local_tail_checks = 0
    for uu, yy, vv in product(triples5, fives7, fives7):
        u = min(uu & children)
        group = {1, 2, 3} if u == 0 else ({4, 5, 6} if u == 2 else columns)
        require(bool(yy & group), "the same given seven-tree has a compatible root")
        y = min(yy & group)
        require(bool(vv & tails7), "its five-child choice meets the fine source")
        v = min(vv & tails7)
        require(u in tails5(y) and v in tails7, "local choices give an actual fine edge")
        local_tail_checks += 1
    require(local_tail_checks == 4410, "exhaustive local tail choice count")

    def full_tree_witness(tree5, tree7):
        require(len(tree5) == 3 and set(tree5) <= set(range(5)), "three five-roots")
        for second in tree5.values():
            require(len(second) == 3 and set(second) <= set(range(5)), "three second digits")
            for last in second.values():
                require(len(set(last)) == 3 and set(last) <= set(range(5)), "three final digits")
        require(len(tree7) == 5 and set(tree7) <= set(range(7)), "five seven-roots")
        for last in tree7.values():
            require(len(set(last)) == 5 and set(last) <= set(range(7)), "five seven-children")
        r = min(set(tree5) & roots)
        a = min(set(tree5[r]) & children)
        u = min(set(tree5[r][a]) & children)
        group = {1, 2, 3} if u == 0 else ({4, 5, 6} if u == 2 else columns)
        y = min(set(tree7) & group)
        v = min(set(tree7[y]) & tails7)
        witness = fine_crt(r + 5*a + 25*u, y + 7*v)
        require(witness in actual, "full product-tree witness is an actual common point")
        return witness

    witness_controls = []
    for i, rr in enumerate(triples5):
        tree5 = {r: {a: triples5[(i+r+a) % 10] for a in triples5[(i+r) % 10]} for r in rr}
        for j, yy in enumerate(fives7):
            tree7 = {y: fives7[(j+y) % 21] for y in yy}
            witness_controls.append(full_tree_witness(tree5, tree7))
    require(len(witness_controls) == 210, "210 complete witness-construction controls")
    projection5 = {x % 125 for x in actual}
    projection7 = {x % 49 for x in actual}
    require(projection5 == {r+5*a+25*u for r, a, u in product(roots, children, children)},
            "standalone five-coordinate projection")
    require(projection7 == {y+7*v for y, v in product(columns, tails7)},
            "standalone seven-coordinate projection")
    require(all(set(t) & columns and set(t) & tails7 for t in combinations(range(7), 3)),
            "standalone ternary seven-tree local intersections")

    law = {x: F(1, 540) for x in points}
    coarse_law = {s: F(1, 54) for s in fibres}
    require(all(sum(w for x, w in law.items() if x % 175 == s) == w0
                for s, w0 in coarse_law.items()), "same-law uniform coarse marginal")
    expected = ((F(1), F(1, 6), F(1, 30)),
                (F(1, 3), F(1, 18), F(1, 90)),
                (F(1, 9), F(1, 54), F(1, 270)),
                (F(1, 18), F(1, 108), F(1, 540)))
    maxima = {d: cylinder_max(law, d) for d in FINE}
    require(all(maxima[5**a * 7**b] == expected[a][b] for a, b in product(range(4), range(3))),
            "exact540-point cylinder maximum matrix")
    center = fine_crt(26, 1)
    require(center in actual, "coherent layout center is an actual point")
    require(all(sum(w for x, w in law.items() if x % d == center % d) == maxima[d] for d in FINE),
            "one coherent layout simultaneously attains all cylinder maxima")
    coarse_maxima = {d: cylinder_max(coarse_law, d) for d in COARSE}
    coarse_upper = sum((coarse_maxima[lcm(d, e)] for d, e in product(COARSE, repeat=2)), F())
    fine_upper = sum((maxima[lcm(d, e)] for d, e in product(FINE, repeat=2)), F())
    require(coarse_upper == centered_moment(coarse_law, COARSE, center) == F(23, 6),
            "exact all-phase coarse Gamma23/6")
    require(fine_upper == centered_moment(law, FINE, center) == F(265, 54) < 9,
            "exact all-phase fine Gamma265/54")
    require(fine_upper-coarse_upper == F(29, 27), "exact common-law tail29/27")
    tail_rows = []
    for a, b, count in ((3, 0, 7), (3, 1, 21), (3, 2, 35), (0, 2, 5), (1, 2, 15), (2, 2, 25)):
        d = 5**a * 7**b
        require(sum(lcm(e, f) == d for e, f in product(FINE, repeat=2)) == count,
                "new LCM multiplicity")
        tail_rows.append({"A": a, "B": b, "ordered_pairs": count,
                          "cylinder_max": str(maxima[d]), "contribution": str(count*maxima[d])})
    return {"actual_residues": points, "source_points": 540, "coarse_points": sorted(fibres),
            "occupied_five_roots": sorted(roots), "robust_coarse_roots": 3,
            "fibre_points": 10, "all_fibre_matching_numbers": 2, "good_coarse_points": good,
            "local_rectangle_checks": 3*10*21, "exhaustive_local_tail_checks": local_tail_checks,
            "complete_tree_witness_controls": len(witness_controls),
            "tree_verification": "Quantified witness construction with exhaustive local intersections; not exhaustive full-tree enumeration.",
            "uniform_weight": "1/540", "coarse_uniform_weight": "1/54",
            "cylinder_maxima": {str(d): str(m) for d, m in maxima.items()},
            "coherent_center": center, "coherent_center_CRT": [26, 1],
            "coarse_Gamma_exact": str(coarse_upper), "fine_Gamma_exact": str(fine_upper),
            "fine_tail_exact": "29/27", "tail_groups": tail_rows,
            "scope": "Refutes automatic matching-three fibre extraction in the abstract actual-source class. This same law satisfies both moment targets; no odd-cover realization is claimed."}


def height_controls():
    # Geometric moments sum_{n>=1} n^j r^n at r=1/3, j=0,...,3.
    r = F(1, 3)
    moments = (r / (1-r), r / (1-r)**2,
               r*(1+r) / (1-r)**3, r*(1+4*r+r*r) / (1-r)**4)
    require(moments == (F(1, 2), F(3, 4), F(3, 2), F(33, 8)), "geometric moments")
    r5_infty = 2*moments[1] + 5*moments[0]
    r7_infty = 2*moments[1] + 3*moments[0]
    x_infty = 4*moments[3] + 24*moments[2] + 22*moments[1] - 15*moments[0]
    require((r5_infty, r7_infty, x_infty) == (4, 3, F(123, 2)), "full tail sums")
    strip_k2 = F(68, 15) + F(4, 15)*4 + F(11, 15)*F(5, 3) + F(20, 15)
    strip_h3 = F(68, 15) + F(4, 15)*F(7, 3) + F(11, 15)*3 + F(21, 15)
    both = F(68, 15) + F(4, 15)*4 + F(11, 15)*3 + F(1, 15)*x_infty
    require(strip_k2 == F(367, 45) < 9 and strip_h3 == F(394, 45) < 9,
            "both unbounded strip constants")
    require(both == F(119, 10) > 9, "full two-height certificate boundary")
    finite = []
    for h, k in product(range(2, 9), range(1, 9)):
        u, v = h-2, k-1
        r5 = sum((F(2*j+5, 3**j) for j in range(1, u+1)), F())
        r7 = sum((F(2*j+3, 3**j) for j in range(1, v+1)), F())
        x = sum((F((2*a+5)*(2*b+3), 3**max(a, b))
                 for a in range(1, u+1) for b in range(1, v+1)), F())
        grouped = F()
        for n in range(1, max(u, v)+1):
            aa, bb = min(n, u), min(n, v)
            pa, pb = min(n-1, u), min(n-1, v)
            coefficient = aa*(aa+6)*bb*(bb+4)-pa*(pa+6)*pb*(pb+4)
            grouped += F(coefficient, 3**n)
        require(grouped == x, "direct double sum versus max-layer grouping")
        bound = F(68, 15) + F(4, 15)*r5 + F(11, 15)*r7 + x/15
        require(bound <= both, "finite bound below full series")
        if k <= 2:
            require(bound <= strip_k2, "finite point of K<=2 strip")
        if h <= 3:
            require(bound <= strip_h3, "finite point of H<=3 strip")
        if (h, k) == (3, 2):
            require(bound == F(322, 45), "one-step matching specialization")
        finite.append({"H": h, "K": k, "bound": str(bound)})
    return {"R5_infinity": str(r5_infty), "R7_infinity": str(r7_infty),
            "X_infinity": str(x_infty), "K_at_most2_bound": str(strip_k2),
            "H_at_most3_bound": str(strip_h3), "full_height_certificate": str(both),
            "finite_double_sum_controls": finite,
            "scope": "Infinite-height statements use geometric-series identities and the ordinary common-law proof."}


def joint_tail_missing_tree(edges):
    """An exact empty 3-by-five-ary-depth2 product witness, or None."""
    for rows in combinations(range(5), 3):
        untouched = {}
        for y in range(7):
            vv = [v for v in range(7)
                  if all((u, y + 7*v) not in edges for u in rows)]
            if len(vv) >= 5:
                untouched[y] = vv[:5]
        if len(untouched) >= 5:
            ys = sorted(untouched)[:5]
            return {"new_five_digits": rows,
                    "seven_tree": {str(y): untouched[y] for y in ys}}
    return None


def joint_tail_flow(edges):
    require(edges and all(type(u) is int and type(z) is int
                         and 0 <= u < 5 and 0 <= z < 49 for u, z in edges),
            "literal joint tail input")
    require(joint_tail_missing_tree(edges) is None, "joint tail product blocker")
    residual, adjacent = {}, defaultdict(list)

    def edge(v, w, cap):
        require((v, w) not in residual and (w, v) not in residual,
                "no duplicate network edge")
        residual[v, w], residual[w, v] = cap, 0
        adjacent[v].append(w); adjacent[w].append(v)

    source, sink = ("s",), ("t",)
    for u in range(5): edge(source, ("u", u), 3)
    for u, z in sorted(edges): edge(("u", u), ("z", z), 9)
    for z in range(49): edge(("z", z), ("y", z % 7), 1)
    for y in range(7): edge(("y", y), sink, 3)
    total = 0
    while total < 9:
        parent = {source: None}; queue = [source]
        for v in queue:
            for w in adjacent[v]:
                if w not in parent and residual[v, w] > 0:
                    parent[w] = v; queue.append(w)
            if sink in parent: break
        require(sink in parent, "blocking joint tail has flow value9")
        v, amount = sink, 9-total
        while parent[v] is not None:
            w = parent[v]; amount = min(amount, residual[w, v]); v = w
        v = sink
        while parent[v] is not None:
            w = parent[v]; residual[w, v] -= amount; residual[v, w] += amount; v = w
        total += amount
    kept = [(u, z) for u, z in sorted(edges)
            if residual[("z", z), ("u", u)] > 0]
    require(len(kept) == 9 and len({z for u, z in kept}) == 9,
            "nine distinct actual joint pairs")
    require(all(sum(v == u for v, z in kept) <= 3 for u in range(5)),
            "new-five cap on the same selected law")
    require(all(sum(z % 7 == y for u, z in kept) <= 3 for y in range(7)),
            "seven-root cap on the same selected law")
    return kept


def joint_prefix_caps():
    return {5**i * 7**j: (F(1, 3**(i+j)) if i <= 2
                         else F(1, 3**(2+max(1, j))))
            for i in range(4) for j in range(3)}


def construct_joint_prefix_law(actual_residues):
    values = list(actual_residues)
    require(values and len(values) == len(set(values))
            and all(type(x) is int and 0 <= x < 6125 for x in values),
            "distinct literal source residues")
    actual = set(values)
    tails = defaultdict(set)
    for x in values: tails[x % 25].add(((x % 125)//25, x % 49))
    good = [b for b in sorted(tails) if joint_tail_missing_tree(tails[b]) is None]
    roots = [r for r in range(5) if sum(b % 5 == r for b in good) >= 3]
    require(len(roots) >= 3, "three roots each with three joint-good prefixes")
    prefixes = [b for r in roots[:3] for b in [z for z in good if z % 5 == r][:3]]
    selected, flows = [], []
    for b in prefixes:
        flow = joint_tail_flow(tails[b])
        for u, z in flow:
            x = fine_crt(b+25*u, z)
            require(x in actual and x % 25 == b, "actual support preserved")
            selected.append(x)
        flows.append({"mod25_prefix": b, "selected_actual_tail_pairs": flow})
    require(len(selected) == len(set(selected)) == 81, "81 selected actual source points")
    law = {x: F(1, 81) for x in selected}
    require(sum(law.values()) == 1, "one normalized common law")
    maxima = {d: cylinder_max(law, d) for d in FINE}
    caps = joint_prefix_caps()
    require(set(caps) == set(FINE), "all twelve original divisors")
    require(all(maxima[d] <= caps[d] for d in FINE), "simultaneous same-law cylinder caps")
    coefficient_sum = sum((2*i+1)*(2*j+1)*caps[5**i*7**j]
                          for i in range(4) for j in range(3))
    lcm_sum = sum((caps[lcm(d, e)] for d, e in product(FINE, repeat=2)), F())
    require(coefficient_sum == lcm_sum == F(8), "complete144 ordered-pair upper bound8")
    actual_upper = sum((maxima[lcm(d, e)] for d, e in product(FINE, repeat=2)), F())
    require(actual_upper <= 8, "actual same-law all-phase bound")
    return {"source_points": len(values), "selected_mod25_prefixes": prefixes,
            "joint_flows": flows, "selected_actual_residues": sorted(selected),
            "point_mass": "1/81", "original_fine_labels": FINE,
            "same_law_cylinder_maxima": {str(d): str(maxima[d]) for d in FINE},
            "same_law_cylinder_caps": {str(d): str(caps[d]) for d in FINE},
            "actual_LCM_upper": str(actual_upper), "uniform_theorem_upper": "8"}


def joint_prefix_540_controls(actual_residues):
    # Reuse empty_good_fibre_countercontrol()['actual_residues']; no second fixture.
    values = list(actual_residues)
    explicit = {x: F(1, 810 if (x % 125)//25 == 1 else 405) for x in values}
    require(len(values) == len(set(values)) == 540, "existing540 consumer")
    require(len({x % 175 for x in values}) == 54, "same54 coarse cells")
    require(sum(explicit.values()) == 1, "explicit common law normalizes")
    require(all(sum(w for x, w in explicit.items() if x % 175 == s) == F(1, 54)
                for s in {x % 175 for x in values}), "explicit law preserves uniform coarse marginal")
    maxima = {d: cylinder_max(explicit, d) for d in FINE}
    caps = joint_prefix_caps()
    require(all(maxima[d] <= caps[d] for d in FINE), "explicit consumer satisfies theorem caps")
    upper = sum((maxima[lcm(d, e)] for d, e in product(FINE, repeat=2)), F())
    center = fine_crt(1, 1)
    lower = centered_moment(explicit, FINE, center)
    require(upper == lower == F(394, 81) < 8, "explicit540 common-law exact Gamma")
    return {"constructor": construct_joint_prefix_law(values),
            "explicit_law": {"point_mass_u_zero_or_two": "1/405", "point_mass_u_one": "1/810",
                             "coarse_marginal": "uniform54", "center": center,
                             "same_law_cylinder_maxima": {str(d): str(maxima[d]) for d in FINE},
                             "Gamma_exact": str(upper)},
            "scope": "ordinary source theorem controls; no minimum-cover provenance or Lean claim"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", help="JSON list of actual fine residues")
    parser.add_argument("--output", help="optional exact JSON output")
    parser.add_argument("--joint-prefix", action="store_true",
                        help="use the joint mod25-fibre constructor for --input")
    args = parser.parse_args()
    if args.joint_prefix and not args.input:
        parser.error("--joint-prefix requires --input")
    if args.input:
        with open(args.input, encoding="utf-8") as stream:
            constructor = construct_joint_prefix_law if args.joint_prefix else construct
            result = {"input": constructor(json.load(stream))}
    else:
        sources = {"aligned": consumer(False), "nonstandard": consumer(True)}
        result = {name: construct(points) for name, points in sources.items()}
        bad_source = sources["nonstandard"]
        target = min(x % 175 for x in bad_source)
        kept = min(x for x in bad_source if x % 175 == target)
        bad_source = [x for x in bad_source if x % 175 != target or x == kept]
        require({x % 175 for x in bad_source} == {x % 175 for x in sources["nonstandard"]},
                "failed-tail control preserves the full coarse projection")
        failed_edges = {((kept % 125) // 25, (kept % 49) // 7)}
        bad_rectangle = empty_rectangle(failed_edges)
        require(bad_rectangle is not None, "one-edge fibre has a missing rectangle")
        try:
            construct(bad_source)
        except ValueError as exc:
            require("misses rectangle" in str(exc), "reject at the actual fine support condition")
        else:
            raise ValueError("failed-tail source unexpectedly accepted")
        result["coarse_only_countercontrol"] = {
            "same_coarse_projection": True, "failed_coarse_residue": target,
            "empty_tail_rectangle": bad_rectangle,
            "scope": "Fails the full tree premise; not a counterexample to the lifting theorem."}
    general_bound = F(46, 9) + F(91, 120) + F(5, 3) + F(7, 9)
    require(general_bound == F(2993, 360) < 9, "broader good-fibre matching bound")
    result["general_good_fibre_bound"] = str(general_bound)
    result["height_strips"] = height_controls()
    result["empty_good_fibre_countercontrol"] = empty_good_fibre_countercontrol()
    result["joint_prefix_control"] = joint_prefix_540_controls(
        result["empty_good_fibre_countercontrol"]["actual_residues"])
    result["scope"] = "Ordinary quantified proof plus exact finite controls; no Lean or minimal odd-cover realization."
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        with open(args.output, "w", encoding="utf-8") as stream:
            stream.write(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
