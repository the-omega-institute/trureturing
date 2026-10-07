"""Exact finite source evidence for TM64, not a controller or supplier service.

Python 3.9+, standard library only. Reuse the existing faithful Clifford
matrices; separately evaluate the TM28 integer normal forms and literal
ordered trees. The consumer uses only H, authentic i and acquired responses.
Hidden sizes are used solely by the experimental original-action simulator.
"""

import argparse
from collections import Counter, defaultdict
import importlib.util
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "tm60_arithmetic", Path(__file__).with_name("h15_joint_cover.py"))
ARITH = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ARITH)
require = ARITH.require
UNIT = ((0, 0, 0),) * 3
CAPS = range(60, 64)
POINTS = tuple((z, w) for z in range(2, 16) for w in range(z + 1, 2 * z))
UPPER = tuple((8, w) for w in range(9, 16)) + ((10, 15), (12, 15), (14, 15))
SYMBOL4 = ((4, 5), (4, 6), (4, 7)) + UPPER


def supplier(z, w):
    if w > 15:
        return 1
    if z <= 8:
        return 1 + (z - 1) % 4
    x, y = z - 8, w - 8
    return (x + 1) // 2 if x % 2 == y % 2 else (y + 1) // 2


def target(z, w):
    """Literal INITIAL target, including the original nested tag-2 pair."""
    if w > 15:
        return (0, 1, 4 * z)
    composition = (4 * (2 * z - w), 4 * (w - z))
    return ((2, (UNIT, composition)) if z + w <= 15
            else (1, composition, 1, 1))


def nf_product(x, y):
    e, k, p = x
    f, ell, q = y
    return ((e + f + p * ell) % 2, k + (-1) ** p * ell, (p + q) % 2)


def normal(word):
    value = (0, 0, 0)
    for leaf in word:
        value = nf_product(value, (0, 0, 1) if leaf == "a" else (0, 1, 1))
    return value


def nf_matrix(value):
    e, k, p = value
    s = ARITH.multiply(ARITH.B, ARITH.A)
    base = s if k >= 0 else tuple(x - y for x, y in zip(s, ARITH.IDENTITY))
    out = ARITH.IDENTITY
    for _ in range(abs(k)):
        out = ARITH.multiply(out, base)
    if p:
        out = ARITH.multiply(out, ARITH.A)
    return tuple((-1) ** e * x for x in out)


def tree(word, balanced=False):
    require(bool(word), "empty actual context/source")
    if len(word) == 1:
        return word
    if balanced:
        cut = len(word) // 2
        return (tree(word[:cut], True), tree(word[cut:], True))
    result = word[0]
    for leaf in word[1:]:
        result = (result, leaf)
    return result


def word_of(t):
    return t if isinstance(t, str) else word_of(t[0]) + word_of(t[1])


def replace(t):
    if isinstance(t, str):
        return "b" if t == "a" else ("b", "a")
    return (replace(t[0]), replace(t[1]))


def omega(z, w, balanced=False):
    r, s = 2 * z - w, w - z
    return tree("a" * (2 * r - 1) + "b" * (2 * s) + "a"
                + "b" * (2 * s - 1) + "a" * (2 * r) + "b", balanced)


def window_check(t):
    """The integer normal form and faithful matrix agree in all 3 windows."""
    values = []
    for _ in range(3):
        word = word_of(t)
        value = normal(word)
        require(nf_matrix(value) == ARITH.leaf_product(word),
                "integer normal form / exact matrix mismatch")
        values.append(value)
        t = replace(t)
    return tuple(values)


def original_action(t, cap, kind, context=None, side="right"):
    if kind == "rho":
        candidate = replace(t)
    else:
        require(context is not None and len(word_of(context)) > 0,
                "nonpositive context requested")
        candidate = (t, context) if side == "right" else (context, t)
    size = len(word_of(candidate))
    accepted = size <= cap
    after = candidate if accepted else t
    require(accepted or after is t, "rejection changed the actual source")
    require(len(word_of(after)) <= cap, "accepted source exceeds H")
    return after, "A" if accepted else "R", size


def prefix_context(cap, symbol):
    if symbol == 4:
        return ("a", "b", "ab", "bb")[cap - 60]
    return "a" * (cap - 4 * (6 + 2 * symbol))


def prefix_entry(cap, z, w):
    """Public source dictionary calculation, not an online size port."""
    symbol = supplier(z, w)
    context = prefix_context(cap, symbol)
    d, e = len(context), len(context) + context.count("b")
    accept_context = 4 * z + d <= cap
    m, n = (4 * z + d, 4 * w + e) if accept_context else (4 * z, 4 * w)
    accept_rho = n <= cap
    branch = ("A" if accept_context else "R") + ("A" if accept_rho else "R")
    return symbol, branch, n if accept_rho else m


def dictionaries(cap):
    data = defaultdict(dict)
    for z, w in POINTS:
        symbol, branch, entry = prefix_entry(cap, z, w)
        mapping = data[(symbol, branch)]
        require(entry not in mapping or mapping[entry] == target(z, w),
                "one branch/entry has distinct initial targets")
        mapping[entry] = target(z, w)
    for symbol in range(1, 5):
        original = {target(z, w) for z, w in POINTS if supplier(z, w) == symbol}
        observed = {v for (i, _), m in data.items() if i == symbol for v in m.values()}
        require(observed == original, "dictionary omitted an initial target")
    return data


def decode_original(symbol, branch, entry, cap):
    if symbol == 4:
        d, e = (len(prefix_context(cap, 4)), cap - 59)
        if branch == "AA":
            w = (entry - e) // 4
            return target(4 if w <= 7 else 8, w)
        require(branch == "AR", "unexpected symbol-4 branch")
        return target((entry - d) // 4, 15)
    cutoff = 6 + 2 * symbol
    material = cap - 4 * cutoff
    if branch == "AA":
        w = (entry - material) // 4
        return target(symbol if w <= 2 * symbol - 1 else 4 + symbol, w)
    if branch == "AR":
        z = (entry - material) // 4
        return target(z, cutoff + 1 if z <= 8 else cutoff + 1 + z % 2)
    if branch == "RA":
        w = entry // 4
        return target(cutoff + 1 if w % 2 or w == cutoff + 2 else cutoff + 2, w)
    require(branch == "RR", "unexpected original TM58 branch")
    return (0, 1, entry)


def replay(cap, z, w, table, balanced):
    initial = omega(z, w, balanced)
    current = initial
    symbol = supplier(z, w)
    emitted_context = tree(prefix_context(cap, symbol))
    current, first, context_candidate = original_action(current, cap, "context", emitted_context)
    material = len(word_of(emitted_context)) if first == "A" else 0
    current, second, rho_candidate = original_action(current, cap, "rho")
    branch = first + second
    entry = len(word_of(current))
    require((symbol, branch, entry) == prefix_entry(cap, z, w),
            "actual ordered-tree prefix / dictionary mismatch")
    feasible = sorted(table[(symbol, branch)])
    accepted_alpha = 0
    responses = branch
    candidates = [context_candidate, rho_candidate]
    equality = sum(x == cap for x in candidates)
    steps = []
    while len(feasible) > 1:
        k = feasible[(len(feasible) + 1) // 2 - 1]
        d = cap - accepted_alpha - k
        require(d > 0 and max(feasible) + accepted_alpha <= cap,
                "threshold context lacks its legal positivity invariant")
        context = tree("a" * d)
        current, response, candidate = original_action(current, cap, "context", context)
        require((response == "A") == (entry <= k), "true threshold guard mismatch")
        before = list(feasible)
        if response == "A":
            accepted_alpha = cap - k
            feasible = [m for m in feasible if m <= k]
        else:
            feasible = [m for m in feasible if m > k]
        require(entry in feasible and max(feasible) + accepted_alpha <= cap,
                "actual entry removed or feasible-size invariant lost")
        require(len(word_of(current)) == entry + accepted_alpha,
                "accepted alpha accounting does not equal actual leaves")
        steps.append({"feasible_before": before, "threshold": k,
                      "context_leaves": d, "candidate_leaves": candidate,
                      "response": response})
        responses += response
        candidates.append(candidate)
        equality += candidate == cap
    # The emitted answer is computed from the acquired singleton, not entry.
    output = decode_original(symbol, branch, feasible[0], cap)
    require(output == table[(symbol, branch)][feasible[0]] == target(z, w),
            "literal INITIAL output mismatch")
    require(len(responses) <= 6, "seventh source call required")
    require((len(responses) - 2) <= (len(table[(symbol, branch)]) - 1).bit_length(),
            "balanced dictionary search exceeded its binary depth")
    final_windows = window_check(current)
    if balanced:
        require(word_of(initial) == word_of(omega(z, w)), "bracketing changed leaves")
    return {"coordinate": [z, w], "symbol": symbol, "initial_target": target(z, w),
            "prefix_context": prefix_context(cap, symbol), "prefix_branch": branch,
            "entry_leaves": entry, "modification_responses": responses,
            "calls": len(responses), "read_calls": 0,
            "accepted_rho": int(second == "A"),
            "accepted_pre_first_rho_leaves": material,
            "candidate_leaves": candidates, "equality_acceptances": equality,
            "threshold_steps": steps, "final_normal_windows": final_windows}


def collision_evidence(cap):
    delta = cap - 60
    out = []
    for case in ("upper-window", "first-splitting-context", "lower-window"):
        points = ((8, 14), (8, 15)) if case != "lower-window" else \
            ((8, 15), (10, 15), (12, 15), (14, 15))
        if case == "upper-window":
            e = delta + 5
            d = (e + 1) // 2
            context_word = "a" * (2 * d - e) + "b" * (e - d)
        elif case == "first-splitting-context":
            context_word = "a" * (delta + 5)
        else:
            context_word = "a" * delta  # delta=0 means no context ACTION.
        states = []
        for z, w in points:
            current = omega(z, w)
            if context_word:
                current, response, _ = original_action(current, cap, "context", tree(context_word))
                require(response == "A", "collision witness context rejected")
            if case == "lower-window":
                current, response, candidate = original_action(current, cap, "rho")
                require(response == "A" and candidate == cap, "lower collision equality lost")
            m = len(word_of(current))
            n = len(word_of(replace(current)))
            current_nf = window_check(current)[0]
            require(n > cap, "collision witness is not current tag zero")
            states.append((m, current_nf))
        require(len(set(states)) == 1 and len({target(*p) for p in points}) == len(points),
                "distinct initial targets did not permanently collide")
        if case == "first-splitting-context":
            t = omega(14, 15)
            after, response, _ = original_action(t, cap, "context", tree(context_word))
            require(response == "R" and after is t, "first D-split witness did not reject row14")
        out.append({"case": case, "points": points, "context_word": context_word,
                    "current_tag0_normal_encoding": (0, states[0][1], states[0][0])})
    return out


def recompute():
    require(len(POINTS) == 105 and len({target(*p) for p in POINTS}) == 56,
            "full composition / target scope changed")
    require(tuple(p for p in POINTS if supplier(*p) == 4) == tuple(sorted(SYMBOL4)),
            "authentic symbol4 is not the thirteen-target dictionary")
    # Check faithfulness and the source identities using existing exact matrices.
    require(ARITH.multiply(ARITH.A, ARITH.A) == ARITH.IDENTITY, "A relation failed")
    require(ARITH.multiply(ARITH.B, ARITH.B) == tuple(-x for x in ARITH.IDENTITY),
            "B relation failed")
    require(tuple(x + y for x, y in zip(ARITH.multiply(ARITH.A, ARITH.B),
                                      ARITH.multiply(ARITH.B, ARITH.A))) == ARITH.IDENTITY,
            "Clifford anticommutator failed")
    for z, w in POINTS:
        source = omega(z, w)
        letters = word_of(source)
        require((letters.count("a"), letters.count("b")) ==
                (4 * (2 * z - w), 4 * (w - z)), "actual source composition mismatch")
        require(window_check(source) == UNIT, "actual source is not unit in all windows")
    caps = []
    for cap in CAPS:
        table = dictionaries(cap)
        sizes = {str(i): {b: len(m) for (j, b), m in sorted(table.items()) if i == j}
                 for i in range(1, 5)}
        require([list(sizes[str(i)].values()) for i in range(1, 5)] ==
                [[3, 1, 6, 7], [5, 3, 4], [7, 5, 2], [9, 4]],
                "full authentic branch cardinalities changed")
        runs = [replay(cap, z, w, table, False) for z, w in POINTS]
        for (z, w), row in zip(POINTS, runs):
            require(replay(cap, z, w, table, True) == row,
                    "two actual source bracketings changed the protocol result")
        worst = [max(row["calls"] for row in runs if row["symbol"] == i)
                 for i in range(1, 5)]
        require(worst == [5, 5, 5, 6], "joint full-source call values changed")
        minimum = (cap - 59 + 1) // 2
        require({row["accepted_pre_first_rho_leaves"] for row in runs
                 if tuple(row["coordinate"]) in UPPER} == {minimum},
                "common-D material not attained")
        # Finite checks of the proof inequalities, not all-policy enumeration.
        delta = cap - 60
        windows = [(u, v) for u in range(delta + 5) for v in range(u, 2 * u + 1)
                   if delta < v <= delta + 4]
        require(min(u for u, _ in windows) == minimum, "material-cone minimum differs")
        for u, v in windows:
            accepts = tuple(p for p in UPPER if 4 * p[1] + v <= cap)
            require(accepts == tuple((8, w) for w in range(9, 15)),
                    "forced first-rho split differs")
        caps.append({"H": cap, "branch_cardinalities": sizes,
                     "per_symbol_worst_calls": worst,
                     "whole_call_histogram": dict(sorted(Counter(row["calls"] for row in runs).items())),
                     "equality_acceptances": sum(row["equality_acceptances"] for row in runs),
                     "common_D_minimum": minimum, "admissible_U_V": windows,
                     "collision_witnesses": collision_evidence(cap), "source_runs": runs})
    return {"scope": "TM64 fixed authentic TM58, complete h15 composition image; ordinary finite evidence",
            "composition_points_per_cap": 105, "caps": caps,
            "actual_bracketing_choices_per_point": 2, "actual_executions": 840,
            "initial_targets": 56, "symbol4_dictionary": SYMBOL4,
            "source_normal_window_checks": 315, "read_calls": 0,
            "accepted_rho_bound": 1, "worst_original_calls": 6,
            "limits": ["All Euler words and all brackets use the paper source correspondence, not this finite enumeration.",
                       "No enumeration of all policies; lower bounds are the paper common-history collision proof.",
                       "No runtime, authentic producer, paid/physical/controller or global-material optimum."]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = recompute()
    canonical = json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2) + "\n"
    if args.write:
        args.certificate.write_text(canonical, encoding="utf-8")
    else:
        require(args.certificate.read_text(encoding="utf-8") == canonical,
                "certificate differs from exact recomputation")
    print("TM64 finite evidence: 420 composition/cap cases, 840 actual bracketed executions; "
          "worst calls (5,5,5,6), common-D material (1,1,2,2); PASS")


if __name__ == "__main__":
    main()
