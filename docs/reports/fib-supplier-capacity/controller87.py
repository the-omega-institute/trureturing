"""TM70 complete 87-state original-source construction, not an optimizer.

Python 3.9+, standard library. Compile fixed c/u/v and then execute its JSON
round-trip on actual ordered trees. Compilation proof columns, coordinates,
sizes, original targets and traces are offline evidence, never controller
ports. Reuse published TM64 source trees/actions and exact Clifford matrices.
"""
import argparse
from collections import Counter, defaultdict
import importlib.util
from itertools import product
import json
from pathlib import Path

_SPEC = importlib.util.spec_from_file_location(
    "tm64_source", Path(__file__).with_name("six_call_material.py"))
SOURCE = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(SOURCE)
require = SOURCE.require
POINTS = SOURCE.POINTS
PREFIX = {
    60: {2: "a" * 17, 3: "ab" + "a" * 7, 4: "ba"},
    61: {2: "a" * 18, 3: "b" + "a" * 9, 4: "ab"},
    62: {2: "a" * 19, 3: "b" + "a" * 10, 4: "baaa"},
    63: {2: "b" + "a" * 19, 3: "ab" + "a" * 10, 4: "baaaa"},
}


def entry_dictionary(cap):
    rows = defaultdict(dict)
    coordinates = defaultdict(dict)
    for z, w in POINTS:
        i = SOURCE.supplier(z, w)
        if i == 1:
            branch, m = ("OA", 4 * w) if w <= 15 else ("OR", 4 * z)
        else:
            word = PREFIX[cap][i]
            d, e = len(word), len(word) + word.count("b")
            a = 4 * z + d <= cap
            r = 4 * w + (e if a else 0) <= cap
            branch = ("A" if a else "R") + ("A" if r else "R")
            m = 4 * w + (e if a else 0) if r else 4 * z + (d if a else 0)
        t = SOURCE.target(z, w)
        require(m not in rows[i, branch] or rows[i, branch][m] == t,
                "prefix entry merges different INITIAL outputs")
        rows[i, branch][m] = t
        coordinates[i, branch][m] = (z, w)
    require([len(row) for _, row in sorted(rows.items())] ==
            [10, 7, 5, 3, 4, 7, 5, 2, 9, 4], "authentic dictionary changed")
    return rows, coordinates


def build(cap):
    require(cap in PREFIX, "only H=60..63 is specified")
    entries, coords = entry_dictionary(cap)
    literals = [SOURCE.target(z, w) for z, w in POINTS if w <= 15]
    literals += [SOURCE.target(z, 16) for z in range(9, 16)]
    require(len(literals) == len(set(literals)) == 56, "literal target census")
    halt = {t: "Q%02d" % j for j, t in enumerate(literals)}
    states = {name: {"Halt": t} for t, name in halt.items()}
    proof_nodes, reader_rows = [], defaultdict(dict)
    W = lambda d: "ba" * (d // 2)

    def write(name, word, a, r=None):
        require(name not in states and word and set(word) <= {"a", "b"},
                "invalid context identity")
        states[name] = {"Request": "right", "word": word,
                        "brackets": "left-associated", "A": a,
                        "R": a if r is None else r, "otherwise": "Q00"}
        return name

    def threshold(i, b, xs, offset=0, path=""):
        if len(xs) == 1:
            return halt[entries[i, b][xs[0]]]
        cut = len(xs) // 2
        pivot = xs[cut - 1]
        d = cap - offset - pivot
        require(d > 0 and max(xs) + offset <= cap, "whole threshold invariant")
        name = "T%d%s:%s" % (i, b, path or "root")
        a = threshold(i, b, xs[:cut], cap - pivot, path + "A")
        r = threshold(i, b, xs[cut:], offset, path + "R")
        write(name, "a" * d, a, r)
        proof_nodes.append([name, i, b, xs, offset, pivot])
        return name

    for d, nxt in ((32, "C16"), (16, "C8"), (8, "C4"), (4, "L")):
        write("C%d" % d, W(d), nxt)
    for d, nxt in ((16, "O8"), (8, "O4"), (4, "L0")):
        write("O%d" % d, W(d), nxt)
    write("J12", W(12), "J16", "C8")
    write("J16", W(16), "C4")
    low4 = [m for m in sorted(entries[4, "AA"]) if m + 16 <= cap]
    require(len(low4) == 5, "F16 accepting support")
    write("F16", "a" * 16, threshold(4, "AA", low4, 16), "C8")
    roots = {(1, "OA"): "C32", (1, "OR"): "O16", (2, "AA"): "C16",
             (3, "AA"): "J12", (3, "AR"): "C16", (4, "AA"): "F16",
             (4, "AR"): "C16"}
    for i, b in ((2, "AR"), (2, "RA"), (3, "RA")):
        roots[i, b] = threshold(i, b, sorted(entries[i, b]))

    def row(reader, nf, t):
        require(nf not in reader_rows[reader], "shared raw Read support collision")
        reader_rows[reader][nf] = halt[t]

    profiles = []
    for i, b, axis, cutoff, ds, slope in (
        (1, "OA", "w", 15, range(10), 2),
        (2, "AA", "w", 10, (0, 1, 2, 3, 7), 2),
        (3, "AA", "w", 12, (0, 1, 2, 3, 4, 7, 8), 2),
        (3, "AR", "z", 12, (0, 1, 2, 3, 5), 2),
        (4, "AA", "w", 14, range(4), 2),
        (4, "AR", "z", 14, range(4), 4),
    ):
        word = "" if i == 1 else PREFIX[cap][i]
        factor_word = (SOURCE.word_of(SOURCE.replace(SOURCE.tree(word)))
                       if b == "AA" else word)
        factor = SOURCE.normal(factor_word)
        family = []
        for D in ds:
            coordinate_value = cutoff - (2 * D if (i, b) == (4, "AR") else D)
            hits = [(m, p) for m, p in coords[i, b].items()
                    if p[1 if axis == "w" else 0] == coordinate_value]
            require(len(hits) == 1, "read row has no unique actual dictionary point")
            m, p = hits[0]
            response = SOURCE.nf_product(factor, (0, slope * D, 0))
            row("L", response, entries[i, b][m])
            family.append([D, response, halt[entries[i, b][m]]])
        coarse = {(e, k % 2, p) for _, (e, k, p), _ in family}
        require(len(coarse) == 1, "family coarse response profile varies")
        profiles.append([i, b, list(next(iter(coarse))), family])
    require(len({tuple(p[2]) for p in profiles}) == 6, "six Read families not separated")
    for z in range(9, 16):
        row("L0", (0, 2 * (15 - z), 0), SOURCE.target(z, 16))
    for name, rows in sorted(reader_rows.items()):
        states[name] = {"Request": "Read", "responses": sorted(rows.items()),
                        "otherwise": "Q00"}
    states["P1"] = {"Request": "rho", "A": roots[1, "OA"],
                    "R": roots[1, "OR"], "otherwise": "Q00"}
    c = ["P1"]
    for i in (2, 3, 4):
        nexts = {}
        for first in "AR":
            bs = {last: roots[i, first + last] for last in "AR" if (i, first + last) in roots}
            if bs:
                name = "P%d%s" % (i, first)
                states[name] = {"Request": "rho", **bs, "otherwise": "Q00"}
                nexts[first] = name
        c.append(write("V%d" % i, PREFIX[cap][i], nexts["A"], nexts.get("R", "Q00")))
    require(len(states) == 87, "compiled state count")
    return {"H": cap, "c": c, "states": states}, {
        "entry_dictionaries": [[i, b, sorted(xs.items())] for (i, b), xs in sorted(entries.items())],
        "threshold_columns": ["state", "i", "branch", "entry_set", "offset", "pivot"],
        "threshold_nodes": sorted(proof_nodes), "Read_families": profiles,
        "prefix_windows": [[i, PREFIX[cap][i], len(PREFIX[cap][i]),
                            len(PREFIX[cap][i]) + PREFIX[cap][i].count("b"),
                            SOURCE.normal(PREFIX[cap][i]),
                            SOURCE.normal(SOURCE.word_of(SOURCE.replace(SOURCE.tree(PREFIX[cap][i]))))]
                           for i in (2, 3, 4)]}


def right_tree(word):
    result = word[-1]
    for leaf in reversed(word[:-1]):
        result = (leaf, result)
    return result


def execute(program, actual, symbol):
    """Controller sees only c(symbol), fixed instruction and actual response.

    Everything else in this routine belongs to the offline source simulator.
    In particular size guards, traces and material counters are not u/v inputs.
    """
    cap, states = program["H"], program["states"]
    k = program["c"][symbol - 1]
    reached, trace = set(), []
    pre, attempted, rho_count = 0, False, 0
    while True:
        reached.add(k)
        ins = states[k]
        if "Halt" in ins:
            return reached, {"output": ins["Halt"], "trace": trace, "calls": len(trace),
                             "pre_first_rho": pre, "accepted_rho": rho_count}
        require(len(trace) < 6, "seventh original call")
        before = actual
        if ins["Request"] == "Read":
            word = SOURCE.word_of(actual)
            nf = SOURCE.normal(word)
            require(SOURCE.nf_matrix(nf) == SOURCE.ARITH.leaf_product(word),
                    "integer Read / exact rational matrix disagree")
            responses = {tuple(n): nxt for n, nxt in ins["responses"]}
            require(nf in responses, "reachable Read uses default transition")
            response, successor, candidate = nf, responses[nf], len(word)
        else:
            context = SOURCE.tree(ins["word"]) if ins["Request"] == "right" else None
            actual, response, candidate = SOURCE.original_action(actual, cap, ins["Request"], context)
            require((response == "A") == (candidate <= cap), "whole equality guard")
            require(response == "A" or actual is before, "rejection loses whole old tree")
            require(response in ins, "reachable modification uses default")
            successor = ins[response]
            if ins["Request"] == "rho":
                attempted = True
                rho_count += response == "A"
            elif not attempted and response == "A":
                pre += len(ins["word"])
        trace.append([k, response, successor, candidate])
        k = successor


def evidence(program):
    reached, fanouts, runs = set(), defaultdict(set), []
    equality, rejected = 0, 0
    for z, w in POINTS:
        base = SOURCE.word_of(SOURCE.omega(z, w))
        # Two different Euler leaf orders; three brackets for each. Rotations
        # of a unit product stay unit in every substitution window.
        variants = []
        for shift in (0, 1):
            word = base[shift:] + base[:shift]
            for bracket, actual in (("left", SOURCE.tree(word)),
                                    ("right", right_tree(word)),
                                    ("balanced", SOURCE.tree(word, True))):
                require(SOURCE.window_check(actual) == SOURCE.UNIT, "non-unit actual source")
                composition = (word.count("a"), word.count("b"))
                m = len(word)
                n = len(SOURCE.word_of(SOURCE.replace(actual)))
                n2 = len(SOURCE.word_of(SOURCE.replace(SOURCE.replace(actual))))
                require(composition == (4 * (2 * z - w), 4 * (w - z)) and
                        (m, n, n2) == (4 * z, 4 * w, 4 * (z + w)),
                        "actual initial resource/composition correspondence")
                literal = ((0, 1, m) if n > program["H"] else
                           (1, composition, 1, 1) if n2 > program["H"] else
                           (2, (SOURCE.UNIT, composition)))
                require(literal == SOURCE.target(z, w), "actual INITIAL target correspondence")
                nodes, result = execute(program, actual, SOURCE.supplier(z, w))
                require(json.dumps(result["output"]) == json.dumps(SOURCE.target(z, w)),
                        "literal INITIAL field order or output changed")
                require(result["accepted_rho"] <= 1, "multiple accepted rho")
                variants.append(result)
                reached.update(nodes)
        require(all(v == variants[0] for v in variants), "word/bracket affects fixed program")
        result = variants[0]
        runs.append({"coordinate": [z, w], "supplier": SOURCE.supplier(z, w), **result})
        for name, response, nxt, candidate in result["trace"]:
            if program["states"][name]["Request"] == "Read":
                fanouts[name].add(tuple(response))
            else:
                equality += candidate == program["H"]
                rejected += response == "R"
    require(reached == set(program["states"]), "unreachable counted complete state")
    types = Counter(ins.get("Request", "Halt") for ins in program["states"].values())
    require(types == {"Halt": 56, "right": 23, "rho": 6, "Read": 2}, "instruction census")
    require(max(r["calls"] for r in runs) == 6, "maximum call count")
    require(max(r["pre_first_rho"] for r in runs) == program["H"] - 43, "sharp material attainment")
    require({k: len(v) for k, v in fanouts.items()} == {"L": 35, "L0": 7}, "actual Read fanout")
    return {"K": len(reached), "instruction_counts": dict(sorted(types.items())),
            "original_call_max": 6, "pre_first_rho_max": program["H"] - 43,
            "accepted_rho_max": max(r["accepted_rho"] for r in runs),
            "actual_Read_fanouts": {k: len(v) for k, v in sorted(fanouts.items())},
            "call_histogram": dict(sorted(Counter(r["calls"] for r in runs).items())),
            "equality_acceptances_in_105_runs": equality,
            "rejected_candidates_in_105_runs": rejected,
            "actual_tree_executions": 630, "unit_window_checks": 1890,
            "trace_columns": ["state", "actual_response", "next", "whole_candidate_or_Read_leaves"],
            "source_runs": runs}


def falsifiers(programs):
    out = []
    for cap, program in programs.items():
        _, a = execute(program, SOURCE.omega(9, 15), 1)
        _, b = execute(program, SOURCE.omega(15, 29), 1)
        ra, rb = a["trace"][-1], b["trace"][-1]
        require(ra[0] == "L" and rb[0] == "L0" and ra[1] == rb[1] == (0, 0, 0)
                and a["output"] != b["output"], "two-Read-address falsifier")
        forced = []
        for z in (8, 10, 12, 14):
            _, r = execute(program, SOURCE.omega(z, 15), 4)
            require(r["trace"][-2][0:2] == ["C4", "R"] and r["calls"] == 6,
                    "4AR forced rejection not charged")
            forced.append([z, r["trace"][-2][3]])
        out.append({"H": cap, "two_reader_points": [[9, 15], [15, 29]],
                    "same_raw_Read": (0, 0, 0), "distinct_outputs": [a["output"], b["output"]],
                    "forced_C4_rejections": forced})
    good = programs[61]
    bad = json.loads(json.dumps(good))
    bad["states"]["V4"]["word"] = "ba"
    _, a = execute(bad, SOURCE.omega(8, 14), 4)
    _, b = execute(good, SOURCE.omega(7, 12), 3)
    require(a["trace"][-1][1] == b["trace"][-1][1] and a["output"] == b["output"]
            and json.dumps(a["output"]) != json.dumps(SOURCE.target(8, 14)),
            "ordered-context mutation did not expose wrong INITIAL output")
    _, plus = execute(good, SOURCE.omega(9, 15), 1)
    _, minus = execute(good, SOURCE.omega(6, 10), 2)
    require(plus["trace"][-1][1] == (0, 0, 0) and minus["trace"][-1][1] == (1, 0, 0)
            and plus["output"] != minus["output"], "raw sign falsifier")
    return {"per_cap": out, "H61_order_mutation": {"points": [[8, 14], [7, 12]],
            "replacement": "V4:ab -> ba", "common_raw_Read": a["trace"][-1][1],
            "wrong_output": a["output"], "required_output": SOURCE.target(8, 14)},
            "H61_sign_pair": [[9, 15], [6, 10]]}


def recompute():
    require(len(POINTS) == 105 and len({SOURCE.target(*p) for p in POINTS}) == 56, "full source census")
    require(len({SOURCE.target(*p) for p in POINTS if SOURCE.target(*p)[0] == 2}) == 14,
            "nested tag2 target census")
    fib_names = {n: ["".join(bits) for bits in product("01", repeat=n)
                     if "11" not in "".join(bits)] for n in (8, 9)}
    require(len(fib_names[8]) == 55 < 56 and len(fib_names[9]) == 89 >= 87,
            "independent static FIB capacity")
    programs, caps = {}, []
    for cap in range(60, 64):
        program, proof = build(cap)
        programs[cap] = json.loads(json.dumps(program))
        caps.append({"H": cap, "controller": programs[cap], "compilation_proof_data": proof,
                     "static_nine_position_names": list(zip(sorted(program["states"]), fib_names[9][:87])),
                     "evidence": evidence(programs[cap])})
    return {"scope": "TM70 complete original-source witness; ordinary paper and finite evidence",
            "runtime_contract": "Only address k and actual response select u/v; c consumes authentic i once. Defaults Q00; Halt update self.",
            "Read_encoding": "Unique actual N(e,k,p)=(-1)^e S^k A^p, exact equality keys, no online factor accumulator",
            "composition_points_per_cap": 105, "hidden_compositions_per_cap": 56,
            "literal_INITIAL_targets": 56, "tag2_targets": 14,
            "finite_source_variants": "omega and its one-leaf cyclic rotation; left/right/balanced brackets",
            "full_source_boundary": "Every Euler word and every bracket uses the paper Atomic360/TM58 correspondence and guard/product induction, not finite exhaustion",
            "static_FIB_capacity": {"eight": 55, "nine": 89, "controller_states": 87,
                                    "literal_Halts": 56, "minimum_name_length": 9, "binary_address_width": 7},
            "caps": caps, "falsifiers": falsifiers(programs)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    canonical = json.dumps(recompute(), ensure_ascii=False, sort_keys=True, separators=(",", ":")) + "\n"
    if args.write:
        args.certificate.write_text(canonical, encoding="utf-8")
    else:
        require(args.certificate.read_text(encoding="utf-8") == canonical, "certificate differs from recomputation")
    print("TM70 PASS: 2520 actual ordered trees; K=(87,87,87,87); "
          "56 Halts,23 contexts,6 rho,2 Reads; calls<=6; pre-rho=(17,18,19,20)")


if __name__ == "__main__":
    main()
