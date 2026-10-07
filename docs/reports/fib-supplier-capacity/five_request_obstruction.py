"""Finite actual-source and guard evidence for TM69's paper obstruction.

Python 3.9+, standard library. Reuse the original ordered-tree emulator,
literal INITIAL fields, authentic supplier and independent Clifford matrices.
This checks necessary arithmetic/source relations, not candidate controllers.
The universal all-visit induction and all Euler/bracket lift are paper proofs.
"""

import argparse
from collections import Counter
from fractions import Fraction
import importlib.util
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "tm69_original_source", Path(__file__).with_name("six_call_material.py"))
SOURCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOURCE)
require = SOURCE.require
POINTS = SOURCE.POINTS
CAPS = range(60, 64)
ACCEPTING = (5, 6, 7, 9, 10, 11, 12, 13, 14)
PAIRS = ((2, ((9, 12), (11, 12))),
         (3, ((7, 13), (10, 13))),
         (4, ((8, 15), (10, 15))))


def context_word(d, e):
    require(1 <= d <= e <= 2 * d, "not a positive actual context mass")
    return "a" * (2 * d - e) + "b" * (e - d)


def folded_behavior(actual, cap):
    word = SOURCE.word_of(actual)
    n = len(SOURCE.word_of(SOURCE.replace(actual)))
    require(n > cap, "collision is not current tag zero")
    normal = SOURCE.normal(word)
    require(SOURCE.nf_matrix(normal) == SOURCE.ARITH.leaf_product(word),
            "current Clifford encodings disagree")
    return (len(word), normal)


def initial_census():
    targets = {SOURCE.target(*p) for p in POINTS}
    loads = [len({SOURCE.target(*p) for p in POINTS
                  if SOURCE.supplier(*p) == i}) for i in range(1, 5)]
    require(len(POINTS) == 105 and len(targets) == 56 and loads == [17, 12, 14, 13],
            "authentic full INITIAL dictionary changed")
    checks = 0
    for z, w in POINTS:
        for balanced in (False, True):
            actual = SOURCE.omega(z, w, balanced)
            word = SOURCE.word_of(actual)
            require((word.count("a"), word.count("b")) ==
                    (4 * (2 * z - w), 4 * (w - z)), "omega composition differs")
            require(SOURCE.window_check(actual) == SOURCE.UNIT,
                    "actual source is not unit in all three windows")
            checks += 3
    rows = {}
    for i in (2, 3, 4):
        distinct = {SOURCE.target(*p): p for p in POINTS if SOURCE.supplier(*p) == i}
        rows[str(i)] = dict(sorted(Counter(p[0] for p in distinct.values()).items()))
    require(rows == {"2": {2: 1, 6: 5, 9: 1, 10: 1, 11: 3, 12: 1},
                     "3": {3: 2, 7: 6, 9: 1, 10: 1, 11: 1, 12: 1, 13: 2},
                     "4": {4: 3, 8: 7, 10: 1, 12: 1, 14: 1}},
            "initial row supports differ")
    return {"composition_points": len(POINTS), "literal_targets": len(targets),
            "authentic_target_loads": loads, "row_target_loads": rows,
            "actual_source_bracket_choices": 2, "unit_window_checks": checks,
            "near_saturation_targets": [SOURCE.target(14, 27), SOURCE.target(15, 29)]}


def first_rho_collisions(cap):
    result = []
    for symbol, pair in PAIRS:
        require(all(SOURCE.supplier(*p) == symbol for p in pair),
                "first-rho pair has wrong authentic supply")
        require(len({SOURCE.target(*p) for p in pair}) == 2,
                "pair has equal INITIAL targets")
        for balanced in (False, True):
            states, candidates, next_sizes = [], [], []
            for p in pair:
                actual = SOURCE.omega(*p, balanced)
                after, response, candidate = SOURCE.original_action(actual, cap, "rho")
                require(response == "A", "first-rho pair did not accept")
                states.append(folded_behavior(after, cap))
                candidates.append(candidate)
                next_sizes.append(len(SOURCE.word_of(SOURCE.replace(after))))
            require(states[0] == states[1], "pair is not a permanent behavior collision")
            result.append({"symbol": symbol, "points": pair, "balanced": balanced,
                           "current_leaves": candidates, "next_leaves": next_sizes,
                           "current_Read_normal": states[0][1]})
    return result


def guard_windows(cap):
    delta, windows, cases = cap - 60, [], 0
    for e_s in range(delta + 1, delta + 5):
        for d_s in range((e_s + 1) // 2, e_s + 1):
            word = context_word(d_s, e_s)
            require(len(word) == d_s and len(word) + word.count("b") == e_s,
                    "actual context mass realization differs")
            require(all(4 * z + d_s <= cap for z, _ in SOURCE.SYMBOL4),
                    "forced s is not accepted on all thirteen targets")
            split = []
            for d_L in range(1, cap + 2):
                n = sum(4 * w + e_s + d_L <= cap for w in ACCEPTING)
                balanced = n in (4, 5)
                interval = cap - 43 - e_s <= d_L <= cap - 36 - e_s
                require(balanced == interval, "true equality guard / interval differs")
                if balanced:
                    require(13 <= d_L <= 23 and d_L != d_s, "L mass separation failed")
                    require(24 + d_L <= cap, "L does not accept symbol2 row6")
                    require(28 + d_L <= cap < 52 + d_L,
                            "L does not split symbol3 rows7 and13")
                    require(52 + d_L > cap, "accepted row11 collision bound failed")
                    split.append([d_L, n, 9 - n])
                cases += 1
            require(len(split) == 8, "balanced integer window is not eight masses")
            windows.append({"d_s": d_s, "e_s": e_s, "balanced_L_guards": split})
    return {"guard_cases": cases, "admissible_s_masses": len(windows),
            "balanced_cases": sum(len(w["balanced_L_guards"]) for w in windows),
            "windows": windows}


def row11_actual_collisions(cap):
    """All bounded L masses that could accept row11, with both actual sides."""
    pair, checks = ((11, 13), (11, 15)), 0
    require(all(SOURCE.supplier(*p) == 2 for p in pair), "row11 supply differs")
    for d in range(13, 24):
        if 44 + d > cap:
            continue
        for e in range(d, 2 * d + 1):
            word = context_word(d, e)
            for balanced in (False, True):
                context = SOURCE.tree(word, balanced)
                for side in ("left", "right"):
                    states = []
                    for p in pair:
                        actual = SOURCE.omega(*p, balanced)
                        after, response, _ = SOURCE.original_action(
                            actual, cap, "context", context, side)
                        require(response == "A", "row11 collision context rejected")
                        states.append(folded_behavior(after, cap))
                    require(states[0] == states[1], "accepted row11 did not collide")
                    checks += 1
    return checks


def near_saturation_checks(cap):
    """Check common accepted operations and permanent rejections on real trees.

    The finite words below corroborate the paper's all-history induction.
    They are not a repeated-Read controller, and no target is output by them.
    """
    delta, checks, equalities = cap - 60, 0, 0
    pair = ((14, 27), (15, 29))
    require(all(SOURCE.supplier(*p) == 1 for p in pair), "near pair supply differs")
    for offset in range(delta + 1):
        for balanced in (False, True):
            for side in ("left", "right"):
                current = [SOURCE.omega(*p, balanced) for p in pair]
                if offset:
                    context = SOURCE.tree("a" * offset, balanced)
                    updates = [SOURCE.original_action(t, cap, "context", context, side)
                               for t in current]
                    require(all(r == "A" for _, r, _ in updates), "common offset rejected")
                    current = [t for t, _, _ in updates]
                require(len(SOURCE.word_of(current[1])) - len(SOURCE.word_of(current[0])) == 4,
                        "near pair leaf difference changed")
                for kind, context in [("rho", None), ("context", SOURCE.tree("a" * 13)),
                                      ("context", SOURCE.tree("b" * 49))]:
                    updates = [SOURCE.original_action(t, cap, kind, context, side) for t in current]
                    require(all(r == "R" and after is before
                                for before, (after, r, _) in zip(current, updates)),
                            "permanent-rejection witness failed")
                    checks += 1
                for d in range(1, delta - offset + 1):
                    for mask in range(2 ** d):
                        word = "".join("b" if mask & (1 << j) else "a" for j in range(d))
                        context = SOURCE.tree(word, balanced)
                        updates = [SOURCE.original_action(t, cap, "context", context, side)
                                   for t in current]
                        require(all(r == "A" for _, r, _ in updates),
                                "acceptance on larger source did not lift")
                        states = [folded_behavior(t, cap) for t, _, _ in updates]
                        require(states[0][1] == states[1][1] and states[1][0] - states[0][0] == 4,
                                "common actual ordered context broke the near invariant")
                        equalities += sum(candidate == cap for _, _, candidate in updates)
                        checks += 1
    return {"actual_relation_checks": checks, "equality_acceptances": equalities,
            "previous_alpha_offsets": list(range(delta + 1)),
            "points": pair, "initial_next_leaves": [108, 116]}


def recompute():
    minima = {}
    for n in (5, 6):
        feasible = [b for b in range(n + 1)
                    if Fraction(n - b, 4) + Fraction(b, 8) <= 1]
        require(min(feasible) == 2 * n - 8, "mixed completed-word arithmetic differs")
        minima[str(n)] = min(feasible)
    require(8 - (2 + 1 + 2 + 1) == 2, "forced modifier-Halt edge budget differs")
    return {"scope": "TM69 necessary actual-source and integer-guard evidence only",
            "census": initial_census(), "mixed_call_no_Read_minima": minima,
            "initial_modifier_Halt_edge_budget": 3, "forced_modifier_Halt_edge_budget": 2,
            "caps": [{"H": cap, "first_rho_collisions": first_rho_collisions(cap),
                      "forced_guard_windows": guard_windows(cap),
                      "row11_actual_collision_checks": row11_actual_collisions(cap),
                      "near_saturation": near_saturation_checks(cap)} for cap in CAPS],
            "limits": ["The universal proof is TM69.2, not finite controller enumeration.",
                       "All Euler words/brackets use Atomic360/TM58 and the paper correspondence.",
                       "Finite near-pair checks do not enumerate all legal histories or Read visits.",
                       "No exact minimum, six-Request witness, paid saving, or Lean/kernel claim."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    canonical = json.dumps(recompute(), ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if args.write:
        args.certificate.write_text(canonical, encoding="utf-8")
    else:
        require(args.certificate.read_text(encoding="utf-8") == canonical,
                "certificate differs from exact recomputation")
    print("TM69 finite actual-source/guard certificate matched")


if __name__ == "__main__":
    main()
