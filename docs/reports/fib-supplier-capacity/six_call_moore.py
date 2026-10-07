"""Concrete original-source Moore tables and exact evidence for TM66.

Python 3.9+, standard library. This constructs two specified policies, not a
generic optimizer. The emulator holds the actual ordered tree; the controller
has only its table address. Hidden source data and verification counters never
select a controller action or transition. Existing TM64 arithmetic supplies
actual trees, substitution, literal targets and two independent E encodings.
"""

import argparse
from collections import Counter, defaultdict
import importlib.util
import json
from pathlib import Path


SPEC = importlib.util.spec_from_file_location(
    "tm64_source_evidence", Path(__file__).with_name("six_call_material.py"))
SOURCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOURCE)
require = SOURCE.require
POINTS = SOURCE.POINTS
BRANCH_COUNTS = ((3, 1, 6, 7), (5, 3, 4, 0),
                 (7, 5, 2, 0), (9, 4, 0, 0))


def prefix(cap, z, w):
    """TM58 prefix dictionary, used only to construct immutable tables."""
    symbol = SOURCE.supplier(z, w)
    material = cap - 4 * (6 + 2 * symbol)
    accepted = 4 * z + material <= cap
    m, n = ((4 * z + material, 4 * w + material)
            if accepted else (4 * z, 4 * w))
    rho = n <= cap
    branch = ("A" if accepted else "R") + ("A" if rho else "R")
    return symbol, branch, n if rho else m


def entry_tables(cap):
    tables = defaultdict(dict)
    for z, w in POINTS:
        symbol, branch, entry = prefix(cap, z, w)
        literal = SOURCE.target(z, w)
        row = tables[(symbol, branch)]
        require(entry not in row or row[entry] == literal,
                "TM58 entry collision between different INITIAL targets")
        row[entry] = literal
    for symbol in range(1, 5):
        counts = tuple(len(tables.get((symbol, b), {}))
                       for b in ("AA", "AR", "RA", "RR"))
        require(counts == BRANCH_COUNTS[symbol - 1], "branch counts differ")
    return tables


def read_signature(delta, z):
    # E=A^delta S^(2(15-z)) for z<15; E=1 at z=15.
    return ((0, (-1) ** delta * 2 * (15 - z), delta % 2)
            if z < 15 else (0, 0, 0))


def build(cap, seven_read=False):
    """Compile the TM66 sparse trees into literal c,u,v tables."""
    states = []

    def allocate(instruction):
        states.append(instruction)
        return len(states) - 1

    targets = sorted({SOURCE.target(z, w) for z, w in POINTS}, key=repr)
    require(len(targets) == 56, "literal target image differs")
    halts = {target: allocate({"Halt": target}) for target in targets}
    roots = [allocate({}) for _ in range(4)]
    shared = None
    if seven_read:
        shared = allocate({"Request": "Read", "responses": [
            [read_signature(cap - 60, z), halts[SOURCE.target(z, 16)]]
            for z in range(9, 16)], "otherwise": roots[0]})
    tables = entry_tables(cap)
    proof_nodes = []

    def search(symbol, branch, candidates, offset):
        if len(candidates) == 1:
            return (shared if seven_read and (symbol, branch) == (1, "RR")
                    else halts[tables[(symbol, branch)][candidates[0]]])
        cut = len(candidates) // 2
        pivot = candidates[cut - 1]
        length = cap - offset - pivot
        require(length > 0 and max(candidates) + offset <= cap,
                "nonpositive context or invalid sparse-search invariant")
        word = "a" * length
        if seven_read and (symbol, branch) == (1, "RR"):
            delta = cap - 60 if offset == 0 else 0
            require(length > delta and (length - delta) % 4 == 0,
                    "RR word has incorrect positive length")
            word = "a" * delta + "ba" * ((length - delta) // 2)
        node = allocate({})
        accept = search(symbol, branch, candidates[:cut], cap - pivot)
        reject = search(symbol, branch, candidates[cut:], offset)
        states[node] = {"Request": "right", "word": word,
                        "brackets": "left-associated", "A": accept,
                        "R": reject, "otherwise": roots[0]}
        proof_nodes.append([node, symbol, branch, list(candidates), offset, pivot])
        return node

    for symbol in range(1, 5):
        context_responses = {}
        for response in "AR":
            branches = {b: tables[(symbol, response + b)] for b in "AR"
                        if (symbol, response + b) in tables}
            if not branches:
                continue
            rho_state = allocate({})
            successors = {b: search(symbol, response + b, sorted(row), 0)
                          for b, row in branches.items()}
            states[rho_state] = {"Request": "rho", "otherwise": roots[0],
                                 **successors}
            context_responses[response] = rho_state
        states[roots[symbol - 1]] = {
            "Request": "right", "word": "a" * (cap - 4 * (6 + 2 * symbol)),
            "brackets": "left-associated", "otherwise": roots[0],
            **context_responses}
    return {"H": cap, "c": roots, "states": states,
            "proof_node_columns": ["state", "i", "branch", "entries", "offset", "pivot"],
            "proof_nodes": sorted(proof_nodes), "shared_Read_state": shared}


def emulate(program, z, w, balanced):
    cap, states = program["H"], program["states"]
    actual = SOURCE.omega(z, w, balanced)
    require(SOURCE.window_check(actual) == SOURCE.UNIT, "nonunit original source")
    initial = SOURCE.target(z, w)
    # c consumes the authentic symbol once. Only k selects all later actions.
    k = program["c"][SOURCE.supplier(z, w) - 1]
    visited, edges, calls, equality, read_values = set(), set(), 0, 0, []
    trace = []
    while True:
        visited.add(k)
        instruction = states[k]
        if "Halt" in instruction:
            require(instruction["Halt"] == initial, "wrong literal INITIAL Halt")
            break
        require(calls < 6, "reachable seventh original call")
        calls += 1
        if instruction["Request"] == "Read":
            response = SOURCE.normal(SOURCE.word_of(actual))
            require(SOURCE.nf_matrix(response) ==
                    SOURCE.ARITH.leaf_product(SOURCE.word_of(actual)),
                    "actual Read disagrees with exact Clifford matrices")
            successors = dict((tuple(o), v) for o, v in instruction["responses"])
            require(response in successors, "unlisted genuine Read response")
            next_state = successors[response]
            read_values.append(response)
            size = len(SOURCE.word_of(actual))
        else:
            context = (SOURCE.tree(instruction["word"])
                       if instruction["Request"] == "right" else None)
            actual, response, size = SOURCE.original_action(
                actual, cap, instruction["Request"], context)
            require(response in instruction, "unlisted actual guard response")
            next_state = instruction[response]
            equality += int(size == cap and response == "A")
        edges.add((k, str(response), next_state))
        trace.append([k, response, next_state, size])
        k = next_state
    SOURCE.window_check(actual)
    return visited, edges, [z, w, calls, equality, trace], read_values


def evidence(program):
    reached, edges, runs, calls = set(), set(), [], Counter()
    shared_values = set()
    for z, w in POINTS:
        left = emulate(program, z, w, False)
        balanced = emulate(program, z, w, True)
        require(left == balanced, "actual bracketing response mismatch")
        reached.update(left[0])
        edges.update(left[1])
        runs.append(left[2])
        calls[left[2][2]] += 1
        shared_values.update(left[3])
    require(reached == set(range(len(program["states"]))), "unreachable counted state")
    requests = sum("Request" in s for s in program["states"])
    seven = program["shared_Read_state"] is not None
    require(requests == 55 + int(seven), "incorrect Request count")
    require(len(program["states"]) == 111 + int(seven), "incorrect Moore count")
    require(max(calls) == 6, "unexpected witness worst calls")
    require(len(shared_values) == (7 if seven else 0), "Read fanout differs")
    return {"Request": requests, "Halt": 56, "K": len(program["states"]),
            "maximum_calls": max(calls), "call_histogram": dict(sorted(calls.items())),
            "actual_response_edges": len(edges), "shared_Read_values": sorted(shared_values),
            "run_columns": ["z", "w", "calls", "equality_accepts", "trace"],
            "trace_columns": ["state", "actual_response", "next_state", "candidate_or_read_size"],
            "runs": runs, "actual_ordered_executions": 210}


def unary_obstruction(cap):
    """Finite corroboration of the arbitrary-context paper obstruction."""
    require({p for p in POINTS if SOURCE.supplier(*p) == 4} == set(SOURCE.SYMBOL4),
            "authentic symbol4 domain differs")
    rho_pair = (SOURCE.omega(8, 15), SOURCE.omega(10, 15))
    after = [SOURCE.original_action(t, cap, "rho") for t in rho_pair]
    require(all(response == "A" for _, response, _ in after), "rho pair not accepted")
    require(all(len(SOURCE.word_of(SOURCE.replace(t))) > cap for t, _, _ in after),
            "rho collision is not tag0")
    require(all(SOURCE.normal(SOURCE.word_of(t)) == (0, 0, 0) for t, _, _ in after),
            "rho collision current E differs")
    require([len(SOURCE.word_of(t)) for t, _, _ in after] == [60, 60],
            "rho collision size differs")
    classes = Counter()
    checked_collisions = 0
    for d in range(1, cap + 2):
        cutoff = (cap - d) // 4
        category = ("unary_R" if cutoff < 4 else "safe_split" if cutoff < 8
                    else "collision" if cutoff < 14 else "unary_A")
        for e in range(d, 2 * d + 1):
            classes[category] += 1
            if cutoff < 8 or cutoff >= 14:
                require(all((4 * z + d <= cap) == (cutoff >= 14)
                            for z, w in SOURCE.UPPER),
                        "rejection-child unary guard differs")
            if category == "collision":
                # All compositions and both sides; E0 is common since initial E0=1.
                context = SOURCE.tree("a" * (2 * d - e) + "b" * (e - d))
                for side in ("left", "right"):
                    result = [SOURCE.original_action(SOURCE.omega(8, w), cap,
                              "context", context, side) for w in (14, 15)]
                    require(all(response == "A" for _, response, _ in result),
                            "collision pair context not accepted")
                    observations = [(SOURCE.normal(SOURCE.word_of(t)),
                                     len(SOURCE.word_of(t))) for t, _, _ in result]
                    require(observations[0] == observations[1], "current tag0 differs")
                    require(all(len(SOURCE.word_of(SOURCE.replace(t))) > cap
                                for t, _, _ in result), "context collision not tag0")
                    checked_collisions += 1
            elif category == "safe_split":
                require(all((4 * z + d <= cap) == (z == 4)
                            for z, w in SOURCE.SYMBOL4), "first split differs")
            else:
                require(all((4 * z + d <= cap) == (category == "unary_A")
                            for z, w in SOURCE.SYMBOL4), "unary guard differs")
    return {"positive_d_range": [1, cap + 1], "e_range": "d..2d",
            "composition_category_counts": dict(sorted(classes.items())),
            "actual_left_right_context_collision_checks": checked_collisions,
            "first_rho_collision_points": [[8, 15], [10, 15]],
            "context_collision_points": [[8, 14], [8, 15]],
            "rejection_child_upper_targets": 10,
            "scope": "Finite guard/collision corroboration; universal graph lower is paper proof."}


def recompute():
    data = {"scope": "TM66 concrete original-source tables; no optimum or kernel claim",
            "caps": [], "all_word_bracket_lift": "Atomic360.2-4, TM30.2, TM47.2, TM58.2",
            "state_table_convention": "c once; literal Request/Halt; unlisted O uses otherwise; Halt update self",
            "response_encoding": "A/R, or exact unique TM28 E normal coordinates (e,k,p)",
            "source_points_per_cap": 105, "hidden_compositions_per_cap": 56}
    for cap in range(60, 64):
        witness, illustration = build(cap), build(cap, True)
        data["caps"].append({"H": cap, "witness": witness,
                             "witness_evidence": evidence(witness),
                             "seven_Read_illustration": illustration,
                             "seven_Read_evidence": evidence(illustration),
                             "unary_obstruction": unary_obstruction(cap)})
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path,
                        default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    canonical = json.dumps(recompute(), ensure_ascii=False, sort_keys=True,
                           separators=(",", ":")) + "\n"
    if args.write:
        args.certificate.write_text(canonical, encoding="utf-8")
    else:
        require(args.certificate.read_text(encoding="utf-8") == canonical,
                "certificate bytes differ from exact recomputation")
    print("TM66 PASS: 1680 actual ordered executions; four 111-state/six-call witnesses; "
          "four 112-state/six-call seven-response illustrations; original unary collisions")


if __name__ == "__main__":
    main()
