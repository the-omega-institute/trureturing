"""Exact actual-source evidence for TM65; Python 3.9+, standard library.

Reuses TM64's original trees, guards, supplier, literal targets and exact
Clifford arithmetic. This is finite mathematical evidence, not a solver,
runtime, authentic producer or enumeration of all words or policies.
"""

import argparse
from collections import Counter, defaultdict
import importlib.util
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "tm64_sources", Path(__file__).with_name("six_call_material.py"))
SRC = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SRC)
require = SRC.require
WITNESSES = ((9, 12), (11, 12), (11, 13), (11, 15))


def prefix_word(cap, symbol):
    if symbol == 1:
        return None  # A genuinely omitted call, never an empty context.
    if symbol == 2:
        return "a" * (cap - 43)
    if symbol == 3:
        return "a" * (cap - 51)
    return SRC.prefix_context(cap, symbol)


def prefix_entry(cap, z, w):
    symbol = SRC.supplier(z, w)
    word = prefix_word(cap, symbol)
    d = len(word) if word is not None else 0
    e = d + (word.count("b") if word is not None else 0)
    first = "O" if word is None else ("A" if 4 * z + d <= cap else "R")
    m, n = (4 * z + d, 4 * w + e) if first == "A" else (4 * z, 4 * w)
    second = "A" if n <= cap else "R"
    return symbol, first + second, n if second == "A" else m


def dictionaries(cap):
    table = defaultdict(dict)
    for z, w in SRC.POINTS:
        symbol, branch, entry = prefix_entry(cap, z, w)
        mapping = table[(symbol, branch)]
        require(entry not in mapping or mapping[entry] == SRC.target(z, w),
                "prefix merged different literal INITIAL targets")
        mapping[entry] = SRC.target(z, w)
    return table


def decode(symbol, branch, entry, cap):
    if symbol == 1:
        if branch == "OR":
            return (0, 1, entry)
        require(branch == "OA", "invalid symbol1 branch")
        w = entry // 4
        z = 5 if w <= 9 else (10 if w in (12, 14) else 9)
    elif symbol == 2:
        if branch == "AA":
            w = (entry - (cap - 43)) // 4
            z = 2 if w == 3 else 6
        elif branch == "AR":
            z = (entry - (cap - 43)) // 4
            w = 12 if z == 9 else 11
        else:
            require(branch == "RA", "invalid symbol2 branch")
            w = entry // 4
            z = 12 if w == 14 else 11
    elif symbol == 3:
        if branch == "AA":
            w = (entry - (cap - 51)) // 4
            z = 3 if w <= 5 else 7
        elif branch == "AR":
            z = (entry - (cap - 51)) // 4
            w = 13 if z in (7, 10, 12) else 14
        else:
            require(branch == "RA", "invalid symbol3 branch")
            z, w = 13, entry // 4
    else:
        return SRC.decode_original(symbol, branch, entry, cap)
    return SRC.target(z, w)


def replay(cap, z, w, table, balanced):
    current = SRC.omega(z, w, balanced)
    symbol = SRC.supplier(z, w)
    word = prefix_word(cap, symbol)
    material, responses, equality = 0, "", 0
    if word is None:
        first = "O"
    else:
        current, first, candidate = SRC.original_action(
            current, cap, "context", SRC.tree(word))
        material = len(word) if first == "A" else 0
        responses += first
        equality += candidate == cap
    current, second, candidate = SRC.original_action(current, cap, "rho")
    responses += second
    equality += candidate == cap
    branch = first + second
    entry = len(SRC.word_of(current))  # Experiment-only; not consumer input.
    require((symbol, branch, entry) == prefix_entry(cap, z, w),
            "actual prefix / public dictionary disagreement")
    feasible, added = sorted(table[(symbol, branch)]), 0
    while len(feasible) > 1:
        k = feasible[(len(feasible) + 1) // 2 - 1]
        d = cap - added - k
        require(d > 0 and max(feasible) + added <= cap,
                "original threshold context is not positive/legal")
        current, response, candidate = SRC.original_action(
            current, cap, "context", SRC.tree("a" * d))
        require((response == "A") == (entry <= k), "true guard differs")
        if response == "A":
            added = cap - k
            feasible = [m for m in feasible if m <= k]
        else:
            feasible = [m for m in feasible if m > k]
        require(entry in feasible and max(feasible) + added <= cap,
                "feasible acquired-size invariant failed")
        require(len(SRC.word_of(current)) == entry + added,
                "actual accepted material differs from accounting")
        responses += response
        equality += candidate == cap
    output = decode(symbol, branch, feasible[0], cap)
    require(output == table[(symbol, branch)][feasible[0]] == SRC.target(z, w),
            "literal INITIAL target or inverse failed")
    require(len(responses) <= 6 and material <= cap - 43,
            "joint material/six-call bound failed")
    # Independent rational matrices check all actual final windows.
    SRC.window_check(current)
    return [z, w, symbol, branch, entry, responses, material, len(responses),
            equality]


def lower_cone(cap):
    """Check the proof inequalities on actual sources, not all histories."""
    delta, rows = cap - 60, []
    for u in range(17 + delta):
        for v in range(u, 2 * u + 1):
            word = "a" * (2 * u - v) + "b" * (v - u)
            points = WITNESSES[:2] if v <= 8 + delta else WITNESSES[2:]
            states = []
            for z, w in points:
                current = SRC.omega(z, w)
                if word:
                    current, response, _ = SRC.original_action(
                        current, cap, "context", SRC.tree(word),
                        side="left" if u % 2 else "right")
                    require(response == "A", "common lower-cone material rejected")
                current, response, _ = SRC.original_action(current, cap, "rho")
                require(response == ("A" if v <= 8 + delta else "R"),
                        "lower obstruction first-rho response differs")
                m = len(SRC.word_of(current))
                n = len(SRC.word_of(SRC.replace(current)))
                require(n > cap, "collision is not current tag0")
                states.append((0, SRC.normal(SRC.word_of(current)), m))
            require(states[0] == states[1] and
                    SRC.target(*points[0]) != SRC.target(*points[1]),
                    "permanent same-history collision failed")
            rows.append([u, v, "accept-column12" if v <= 8 + delta
                         else "reject-row11", states[0]])
    # The first distinguishing context must accept at least cap-43 leaves.
    boundary = SRC.tree("a" * (cap - 43))
    a, ra, _ = SRC.original_action(SRC.omega(9, 12), cap, "context", boundary)
    b, rb, _ = SRC.original_action(SRC.omega(11, 12), cap, "context", boundary)
    require(ra == "A" and rb == "R" and
            len(SRC.word_of(a)) == 36 + cap - 43 and
            len(SRC.word_of(b)) == 44, "first context-split boundary differs")
    return rows


def recompute():
    require(len(SRC.POINTS) == 105 and
            len({SRC.target(*p) for p in SRC.POINTS}) == 56,
            "complete actual composition/target domain changed")
    require(all(SRC.supplier(*p) == 2 for p in WITNESSES),
            "lower witnesses are not authentic symbol2")
    for z, w in SRC.POINTS:
        current = SRC.omega(z, w)
        word = SRC.word_of(current)
        require((word.count("a"), word.count("b")) ==
                (4 * (2 * z - w), 4 * (w - z)), "source composition differs")
        require(SRC.window_check(current) == SRC.UNIT,
                "actual source lacks three unit windows")
    caps = []
    for cap in SRC.CAPS:
        table = dictionaries(cap)
        sizes = {str(i): {b: len(m) for (j, b), m in sorted(table.items()) if i == j}
                 for i in range(1, 5)}
        require([list(sizes[str(i)].values()) for i in range(1, 5)] ==
                [[10, 7], [5, 3, 4], [7, 5, 2], [9, 4]],
                "actual branch dictionary cardinalities differ")
        runs = [replay(cap, z, w, table, False) for z, w in SRC.POINTS]
        for (z, w), row in zip(SRC.POINTS, runs):
            require(replay(cap, z, w, table, True) == row,
                    "source brackets affected acquired results")
        material = [max(row[6] for row in runs if row[2] == i) for i in range(1, 5)]
        calls = [max(row[7] for row in runs if row[2] == i) for i in range(1, 5)]
        require(material == [0, cap - 43, cap - 51, (cap - 58) // 2] and
                calls == [5, 5, 5, 6], "joint attaining coordinates differ")
        caps.append({"H": cap, "worst_accepted_pre_first_rho": max(material),
                     "policy_per_symbol_material": material,
                     "policy_per_symbol_calls": calls,
                     "branch_cardinalities": sizes,
                     "call_histogram": dict(sorted(Counter(row[7] for row in runs).items())),
                     "equality_acceptances_one_bracketing": sum(row[8] for row in runs),
                     "source_runs": runs, "lower_material_cone": lower_cone(cap)})
    return {"scope": "TM65 complete U_H, fixed authentic TM58, INITIAL target, original actions",
            "caps": caps, "composition_points": 105, "initial_targets": 56,
            "actual_policy_executions": 840, "initial_window_checks": 315,
            "lower_witnesses": WITNESSES,
            "source_run_columns": ["z", "w", "symbol", "prefix_branch", "entry_leaves",
                                   "real_response_word", "pre_first_rho_leaves", "calls",
                                   "equality_acceptances"],
            "limits": ["Universal words, brackets and policies require the paper proof.",
                       "Per-symbol numbers are this policy's values, not separate optima.",
                       "No paid, physical, controller, producer or Lean/kernel claim."]}


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
    print("TM65 actual-source finite evidence: material (17,18,19,20), "
          "joint worst calls 6; 840 actual policy executions; PASS")


if __name__ == "__main__":
    main()
