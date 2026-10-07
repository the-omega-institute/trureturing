"""TM68 fixed original-source Read witnesses, not a controller optimizer.

Python 3.9+, standard library. Compile explicit immutable c/u/v tables, then
execute those tables on actual ordered trees with whole guards. Reuse TM64's
literal targets, authentic supplier, recursive rho and faithful rational
Clifford matrices. Proof labels are compilation/evidence data, never inputs
to the running controller. Only its table address selects each instruction.
"""

import argparse
from collections import Counter, defaultdict
import importlib.util
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "tm64_actual_sources", Path(__file__).with_name("six_call_material.py"))
SOURCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOURCE)
require = SOURCE.require
POINTS = SOURCE.POINTS


def target_order():
    finite = [SOURCE.target(z, w) for z, w in POINTS if w <= 15]
    folded = [SOURCE.target(z, 16) for z in range(9, 16)]
    require(len(finite) == 49 and len(set(finite + folded)) == 56,
            "literal INITIAL target image differs")
    return finite + folded


def prefix_word(cap, symbol):
    if cap == 60:
        return {2: "a" * 18, 3: "a" * 9, 4: "ba"}[symbol]
    return "a" * (cap - 4 * (6 + 2 * symbol))


def entries(cap):
    """Original supplier/whole-prefix arithmetic, compiled before execution."""
    table = defaultdict(dict)
    for z, w in POINTS:
        i = SOURCE.supplier(z, w)
        if i == 1:
            b, m = ("OA", 4 * w) if w <= 15 else ("OR", 4 * z)
        else:
            word = prefix_word(cap, i)
            d, e = len(word), len(word) + word.count("b")
            first = 4 * z + d <= cap
            current, candidate = ((4 * z + d, 4 * w + e)
                                  if first else (4 * z, 4 * w))
            second = candidate <= cap
            b = ("A" if first else "R") + ("A" if second else "R")
            m = candidate if second else current
        literal = SOURCE.target(z, w)
        require(m not in table[(i, b)] or table[(i, b)][m] == literal,
                "branch/entry collision between INITIAL targets")
        table[(i, b)][m] = literal
    require([len(table[(i, b)]) for i, b in sorted(table)] ==
            [10, 7, 5, 3, 4, 7, 5, 2, 9, 4], "prefix dictionary differs")
    return table


def power(k, sign=0, odd=0):
    return (sign, k, odd)


def build(cap):
    require(cap in range(60, 64), "only four fixed public caps are specified")
    delta, table, states, names = cap - 60, entries(cap), {}, {}
    literals = target_order()
    halts = {t: f"H{j:02d}" for j, t in enumerate(literals)}
    for literal, name in halts.items():
        states[name] = {"Halt": literal}
    reader_rows = defaultdict(dict)

    def context(name, word, accept, reject=None):
        require(name not in states and bool(word) and set(word) <= {"a", "b"},
                "duplicate state or illegal positive word")
        states[name] = {"Request": "right", "word": word,
                        "brackets": "left-associated", "A": accept,
                        "R": accept if reject is None else reject,
                        "otherwise": "H00"}
        return name

    def halt(i, b, m):
        return halts[table[(i, b)][m]]

    def read_row(reader, response, i, b, m):
        successor = halt(i, b, m)
        require(response not in reader_rows[reader] or
                reader_rows[reader][response] == successor,
                "actual Read collision between different literal Halts")
        reader_rows[reader][response] = successor

    def chain(stem, words, end):
        for j, word in enumerate(words):
            context(f"{stem}:{j}", word,
                    f"{stem}:{j + 1}" if j + 1 < len(words) else end)
        return f"{stem}:0"

    proof_nodes = []

    def threshold(i, b, candidates, offset=0, path=""):
        if len(candidates) == 1:
            return halt(i, b, candidates[0])
        cut = len(candidates) // 2
        pivot = candidates[cut - 1]
        length = cap - offset - pivot
        require(length > 0 and max(candidates) + offset <= cap,
                "nonpositive threshold or lost whole-size invariant")
        name = f"T:{i}:{b}:{path or 'root'}"
        a = threshold(i, b, candidates[:cut], cap - pivot, path + "A")
        r = threshold(i, b, candidates[cut:], offset, path + "R")
        context(name, "a" * length, a, r)
        proof_nodes.append([name, i, b, candidates, offset, pivot])
        return name

    W = lambda d: "ba" * (d // 2)
    N = lambda d: "ab" * (d // 2)
    if cap == 60:
        names[(1, "OA")] = chain("OA", [W(d) for d in (32, 16, 8, 4)], "L")
        names[(1, "OR")] = chain("OR", [W(d) for d in (16, 8, 4)], "L0")
        names[(2, "AA")] = chain("2AA", [W(d) for d in (16, 8, 4)], "L")
        names[(3, "AR")] = chain("3AR", [W(d) for d in (16, 8, 4)], "L")
        context("3AA:12", W(12), "3AA:16", "3AA:8")
        context("3AA:16", W(16), "3AA:4")
        context("3AA:8", W(8), "3AA:4")
        context("3AA:4", W(4), "L")
        names[(3, "AA")] = "3AA:12"
        names[(4, "AR")] = chain("4AR", [W(16), W(8)], "L")
        low = [m for m in sorted(table[(4, "AA")]) if m + 16 <= cap]
        require(len(low) == 5, "4AA split differs")
        a = threshold(4, "AA", low, 16)
        r = chain("4AA", [N(8), N(4)], "L")
        context("4AA:split", "a" * 16, a, r)
        names[(4, "AA")] = "4AA:split"
        for w in range(6, 16):
            read_row("L", power(2 * (15 - w)), 1, "OA", 4 * w)
        for w in (3, 7, 8, 9, 10):
            read_row("L", power(2 * (10 - w), 1), 2, "AA", 4 * w + 18)
        for w in (4, 5, 8, 9, 10, 11, 12):
            read_row("L", power(1 - 2 * (12 - w), odd=1), 3, "AA", 4 * w + 9)
        for z in (7, 9, 10, 11, 12):
            read_row("L", power(-2 * (12 - z), odd=1), 3, "AR", 4 * z + 9)
        for z in (8, 10, 12, 14):
            read_row("L", power(1 + 2 * (14 - z)), 4, "AR", 4 * z + 2)
        for w in (11, 12, 13, 14):
            read_row("L", power(2 + 2 * (14 - w), odd=1), 4, "AA", 4 * w + 3)
    else:
        # Five actual writer/reader states are shared across disjoint E supports.
        names[(1, "OA")] = chain("C", [W(d) for d in (32, 16, 8, 4)], "L")
        names[(1, "OR")] = chain("OR", [W(d) for d in (16, 8, 4)], "L0")
        c8, c4 = "C:2", "C:3"
        context("J16", W(16), "J12", c8)
        context("J12", W(12), c4)
        names[(3, "AA")] = "J16"
        v2 = N(8) if delta == 2 else "aabbabab"
        context("K16", W(16), halt(2, "AA", 32 + delta), "K8")
        context("K8", v2, c4, "K4")
        context("K4", W(4), halt(2, "AA", 56 + delta), halt(2, "AA", 60 + delta))
        names[(2, "AA")] = "K16"
        v3 = N(8) if delta == 2 else "aabbbaba"
        context("R16", W(16), halt(3, "AR", 40 + delta), "R8")
        context("R8", v3, c4, "R4")
        context("R4", W(4), halt(3, "AR", 56 + delta), halt(3, "AR", 60 + delta))
        names[(3, "AR")] = "R16"
        v4 = "aa" + "ba" * 7 if delta == 2 else "aabb" + "ba" * 6
        context("T16", v4, c8, "T8")
        context("T8", W(8), halt(4, "AR", 52 + delta), halt(4, "AR", 60 + delta))
        names[(4, "AR")] = "T16"
        bdelta, adelta = SOURCE.normal("b" * delta), SOURCE.normal("a" * delta)
        mul = SOURCE.nf_product
        for w in range(6, 16):
            read_row("L", power(2 * (15 - w)), 1, "OA", 4 * w)
        for m, e in zip((28, 32, 44, 48, 52, 56, 60), (16, 14, 8, 6, 4, 2, 0)):
            read_row("L", mul(bdelta, power(e)), 3, "AA", m + delta)
        for m, e in ((48, 0), (52, -2)):
            response = (power(e - 2, 1) if delta == 2
                        else mul(bdelta, power(e, 1)))
            read_row("L", response, 2, "AA", m + delta)
        for m, e in ((48, 4), (52, 2)):
            response = (power(e - 6) if delta == 2
                        else mul(adelta, power(e, 1)))
            read_row("L", response, 3, "AR", m + delta)
        for m, e in ((36, 11), (44, 7)):
            response = (power(e) if delta == 2 else mul(adelta, power(e - 1, 1)))
            read_row("L", response, 4, "AR", m + delta)

    for z in range(9, 16):
        read_row("L0", power(2 * (15 - z)), 1, "OR", 4 * z)
    for key, row in sorted(table.items()):
        if key not in names:
            names[key] = threshold(*key, sorted(row))
    roots = []
    for i in range(1, 5):
        if i == 1:
            states["P:1"] = {"Request": "rho", "A": names[(1, "OA")],
                              "R": names[(1, "OR")], "otherwise": "H00"}
        else:
            successors = {}
            for first in "AR":
                branches = {b: names[(i, first + b)] for b in "AR"
                            if (i, first + b) in names}
                if branches:
                    name = f"P:{i}:rho:{first}"
                    states[name] = {"Request": "rho", **branches, "otherwise": "H00"}
                    successors[first] = name
            context(f"P:{i}", prefix_word(cap, i), successors["A"], successors.get("R", "H00"))
        roots.append(f"P:{i}")
    for reader, row in sorted(reader_rows.items()):
        states[reader] = {"Request": "Read", "responses": [
            [response, successor] for response, successor in sorted(row.items())],
            "otherwise": "H00"}
    return {"H": cap, "c": roots, "states": states,
            "target_order": literals,
            "entry_dictionaries": [[i, b, [[m, literal] for m, literal in sorted(row.items())]]
                                   for (i, b), row in sorted(table.items())],
            "threshold_proof_columns": ["state", "i", "branch", "entries", "accepted_offset", "pivot"],
            "threshold_proof_nodes": sorted(proof_nodes)}


def right_tree(word):
    result = word[-1]
    for leaf in reversed(word[:-1]):
        result = (leaf, result)
    return result


def emulate(program, z, w, brackets):
    word = SOURCE.word_of(SOURCE.omega(z, w))
    actual = SOURCE.tree(word) if brackets == "left" else right_tree(word)
    require(SOURCE.window_check(actual) == SOURCE.UNIT, "actual initial source not unit")
    composition = (word.count("a"), word.count("b"))
    m = len(word)
    n = len(SOURCE.word_of(SOURCE.replace(actual)))
    n2 = len(SOURCE.word_of(SOURCE.replace(SOURCE.replace(actual))))
    require(composition == (4 * (2 * z - w), 4 * (w - z)) and
            (m, n, n2) == (4 * z, 4 * w, 4 * (z + w)),
            "actual initial composition/substitution resources differ")
    initial = SOURCE.target(z, w)
    actual_literal = ((0, 1, m) if n > program["H"] else
                      (1, composition, 1, 1) if n2 > program["H"] else
                      (2, (SOURCE.UNIT, composition)))
    require(actual_literal == initial, "actual INITIAL literal/order differs")
    k = program["c"][SOURCE.supplier(z, w) - 1]
    states, seen, trace, reads = program["states"], set(), [], []
    material, rho_attempted, accepted_rho = 0, False, 0
    while True:
        seen.add(k)
        ins = states[k]
        if "Halt" in ins:
            require(json.dumps(ins["Halt"]) == json.dumps(initial),
                    "wrong literal INITIAL target")
            break
        require(len(trace) < 6, "seventh original call")
        if ins["Request"] == "Read":
            response = SOURCE.normal(SOURCE.word_of(actual))
            require(SOURCE.nf_matrix(response) == SOURCE.ARITH.leaf_product(SOURCE.word_of(actual)),
                    "actual Read disagrees with independent rational matrices")
            row = dict((tuple(o), t) for o, t in ins["responses"])
            require(response in row, "actual Read falls through total-table default")
            successor, size = row[response], len(SOURCE.word_of(actual))
            reads.append([k, response])
        else:
            context = SOURCE.tree(ins["word"]) if ins["Request"] == "right" else None
            actual, response, size = SOURCE.original_action(actual, program["H"], ins["Request"], context)
            require(response in ins, "actual guard falls through total-table default")
            successor = ins[response]
            if ins["Request"] == "rho":
                rho_attempted = True
                accepted_rho += response == "A"
            elif not rho_attempted and response == "A":
                material += len(ins["word"])
        trace.append([k, response, successor, size])
        k = successor
    require(rho_attempted and accepted_rho <= 1 and len(reads) <= 1,
            "rho/Read original contract differs")
    return seen, {"coordinate": [z, w], "initial_target": initial, "calls": len(trace),
                  "accepted_pre_first_rho_leaves": material, "accepted_rho": accepted_rho,
                  "trace": trace, "Read_responses": reads}


def evidence(program):
    reached, fanouts, edges, runs = set(), defaultdict(set), set(), []
    for z, w in POINTS:
        left, lrow = emulate(program, z, w, "left")
        right, rrow = emulate(program, z, w, "right")
        require((left, lrow) == (right, rrow), "ordered bracketing changes responses/output")
        reached.update(left)
        runs.append(lrow)
        for k, response in lrow["Read_responses"]:
            fanouts[k].add(response)
        for k, response, successor, size in lrow["trace"]:
            edges.add((k, str(response), successor))
    require(reached == set(program["states"]), "counted state has no actual source")
    req = sum("Request" in s for s in program["states"].values())
    expected = 43 if program["H"] == 60 else 42
    require(req == expected and len(program["states"]) == 56 + expected, "complete state count differs")
    require(max(r["calls"] for r in runs) == 6, "worst call count differs")
    require({k: len(v) for k, v in fanouts.items()} ==
            {"L": 35 if program["H"] == 60 else 23, "L0": 7}, "actual Read fanouts differ")
    material = max(r["accepted_pre_first_rho_leaves"] for r in runs)
    require(material == {60: 18, 61: 21, 62: 22, 63: 23}[program["H"]],
            "separate material coordinate differs")
    return {"Request": req, "Halt": 56, "K": 56 + req, "all_states_reachable": True,
            "maximum_original_calls": 6, "accepted_pre_first_rho_maximum": material,
            "call_histogram": dict(sorted(Counter(r["calls"] for r in runs).items())),
            "actual_Read_fanouts": {k: len(v) for k, v in sorted(fanouts.items())},
            "actual_response_edges": len(edges), "ordered_tree_executions": 210,
            "trace_columns": ["state", "actual_response", "successor", "whole_candidate_or_Read_leaves"],
            "runs": runs}


def recompute():
    require(len(POINTS) == 105, "full actual composition count differs")
    caps = []
    for cap in range(60, 64):
        # Execute the serialized c/u/v tables, not live compiler closures.
        program = json.loads(json.dumps(build(cap)))
        caps.append({"H": cap, "controller": program, "evidence": evidence(program)})
    return {"scope": "TM68 explicit original-source six-call witnesses; no optimum/kernel/paid claim",
            "response_encoding": "A/R, or unique actual Clifford N(e,k,p)=(-1)^e S^k A^p",
            "controller_convention": "c consumes authentic i once; only state/actual response update; otherwise H00; Halt update self",
            "target_order": "49 finite (z,w) in lexicographic order, then Z(9)..Z(15)",
            "source_points_per_cap": 105, "hidden_compositions_per_cap": 56,
            "full_word_bracket_scope": "Paper TM68: Atomic360, TM58.2 and actual tree guard/product induction",
            "caps": caps}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    canonical = json.dumps(recompute(), ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"
    if args.write:
        args.certificate.write_text(canonical, encoding="utf-8")
    else:
        require(args.certificate.read_text(encoding="utf-8") == canonical,
                "certificate differs from exact actual-tree recomputation")
    print("TM68 PASS: 840 actual ordered trees; K=(99,98,98,98); calls<=6; pre-rho material=(18,21,22,23)")


if __name__ == "__main__":
    main()
