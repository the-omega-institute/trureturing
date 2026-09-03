#!/usr/bin/env python3
"""Research driver for the typed golden-ratio base-4 DFAO lower bound.

The script generates exact Zeckendorf inputs and golden-ratio digits, builds a
unique prefix trie, emits an exact typed partial-DFAO identification CNF, and
runs a counterexample-guided finite-sample search with CaDiCaL.

This is a discovery tool. Any lower bound promoted to theorem status must later
ship the exact sample, encoder-correctness proof, and a replayable UNSAT proof.
"""

from __future__ import annotations

import argparse
import json
import math
import subprocess
import tempfile
import time
from collections import defaultdict
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
from typing import Dict, List, Mapping, Optional, Sequence, Set, Tuple

Word = Tuple[int, ...]


def fibs_upto(n: int) -> List[int]:
    if n < 0:
        raise ValueError("n must be nonnegative")
    fibs = [0, 1]
    while fibs[-1] <= n:
        fibs.append(fibs[-1] + fibs[-2])
    return fibs


def zeckendorf_indices(n: int) -> List[int]:
    """Canonical decreasing Fibonacci indices, using F_2 = 1."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    if n == 0:
        return []
    fibs = fibs_upto(n)
    k = len(fibs) - 1
    if fibs[k] > n:
        k -= 1
    result: List[int] = []
    while n:
        while fibs[k] > n:
            k -= 1
        if k < 2:
            raise AssertionError("Zeckendorf index below F_2")
        result.append(k)
        n -= fibs[k]
        k -= 2
    return result


def zeckendorf_word(n: int) -> Word:
    """Most-significant-first canonical Zeckendorf word for positive n."""
    indices = zeckendorf_indices(n)
    if not indices:
        return ()
    occupied = set(indices)
    return tuple(1 if k in occupied else 0 for k in range(indices[0], 1, -1))


def golden_floor(n: int) -> int:
    """Exact floor(n * phi), phi = (1 + sqrt(5))/2."""
    if n < 0:
        raise ValueError("n must be nonnegative")
    return (n + math.isqrt(5 * n * n)) // 2


def golden_digit(base: int, index: int) -> int:
    if base < 2 or index < 0:
        raise ValueError("base >= 2 and index >= 0 required")
    return golden_floor(base ** (index + 1)) - base * golden_floor(base**index)


def make_samples(base: int, indices: Sequence[int]) -> Tuple[List[Word], List[int]]:
    words = [zeckendorf_word(base**i) for i in indices]
    labels = [golden_digit(base, i) for i in indices]
    return words, labels


@dataclass(frozen=True)
class Trie:
    nodes: Tuple[Word, ...]
    node_id: Mapping[Word, int]
    edges: Tuple[Tuple[int, int, int], ...]
    node_type: Tuple[int, ...]
    terminal: Mapping[int, int]


def build_trie(words: Sequence[Word], labels: Sequence[int]) -> Trie:
    prefixes: Set[Word] = {()}
    terminal_word: Dict[Word, int] = {}
    for word, label in zip(words, labels):
        for cut in range(len(word) + 1):
            prefixes.add(word[:cut])
        old = terminal_word.get(word)
        if old is not None and old != label:
            raise ValueError("same sample word has contradictory outputs")
        terminal_word[word] = label

    nodes = tuple(sorted(prefixes, key=lambda word: (len(word), word)))
    node_id = {word: idx for idx, word in enumerate(nodes)}
    edges: List[Tuple[int, int, int]] = []
    for word in nodes:
        parent = node_id[word]
        for symbol in (0, 1):
            child_word = word + (symbol,)
            child = node_id.get(child_word)
            if child is not None:
                edges.append((parent, symbol, child))
    node_type = tuple(0 if not word or word[-1] == 0 else 1 for word in nodes)
    terminal = {node_id[word]: label for word, label in terminal_word.items()}
    return Trie(nodes, node_id, tuple(edges), node_type, terminal)


@dataclass(frozen=True)
class ConflictData:
    adjacency: Tuple[frozenset[int], ...]
    witness: Mapping[Tuple[int, int], Tuple[Word, int, int]]


def build_common_suffix_conflicts(
    words: Sequence[Word], labels: Sequence[int], trie: Trie
) -> ConflictData:
    adjacency: List[Set[int]] = [set() for _ in trie.nodes]
    witness: Dict[Tuple[int, int], Tuple[Word, int, int]] = {}
    for left, right in combinations(range(len(words)), 2):
        if labels[left] == labels[right]:
            continue
        a, b = words[left], words[right]
        common = 0
        limit = min(len(a), len(b))
        while common < limit and a[-1 - common] == b[-1 - common]:
            common += 1
        for suffix_length in range(common + 1):
            u = a if suffix_length == 0 else a[:-suffix_length]
            v = b if suffix_length == 0 else b[:-suffix_length]
            ui, vi = trie.node_id[u], trie.node_id[v]
            if ui == vi:
                raise AssertionError("contradictory sample generated a self conflict")
            adjacency[ui].add(vi)
            adjacency[vi].add(ui)
            key = (ui, vi) if ui < vi else (vi, ui)
            suffix = () if suffix_length == 0 else a[-suffix_length:]
            previous = witness.get(key)
            if previous is None or len(suffix) < len(previous[0]):
                witness[key] = (suffix, left, right)
    return ConflictData(tuple(frozenset(x) for x in adjacency), witness)


def triangle_containing(
    conflict: ConflictData, trie: Trie, required: Optional[int], node_type: int
) -> Optional[Tuple[int, int, int]]:
    candidates = [
        i
        for i, typ in enumerate(trie.node_type)
        if typ == node_type and conflict.adjacency[i]
    ]
    firsts = [required] if required is not None and required in candidates else candidates
    if required is not None and required not in candidates:
        return None
    for a in firsts:
        neighbours = [b for b in conflict.adjacency[a] if trie.node_type[b] == node_type]
        neighbour_set = set(neighbours)
        for b in neighbours:
            for c in conflict.adjacency[b]:
                if c in neighbour_set and c != a and c != b:
                    return (a, b, c)
    return None


class CNF:
    def __init__(self) -> None:
        self._next_var = 1
        self.variables: Dict[Tuple[object, ...], int] = {}
        self.clauses: List[Tuple[int, ...]] = []

    def var(self, *key: object) -> int:
        full = tuple(key)
        value = self.variables.get(full)
        if value is None:
            value = self._next_var
            self._next_var += 1
            self.variables[full] = value
        return value

    def add(self, *literals: int) -> None:
        if any(lit == 0 for lit in literals):
            raise ValueError("literal zero is invalid inside a clause")
        self.clauses.append(tuple(literals))

    @property
    def max_var(self) -> int:
        return self._next_var - 1

    def exactly_one_pairwise(self, variables: Sequence[int]) -> None:
        if not variables:
            self.add()
            return
        self.add(*variables)
        for left, right in combinations(variables, 2):
            self.add(-left, -right)

    def at_most_one_pairwise(self, variables: Sequence[int]) -> None:
        for left, right in combinations(variables, 2):
            self.add(-left, -right)

    def write_dimacs(self, path: Path) -> None:
        with path.open("w", encoding="ascii") as handle:
            handle.write(f"p cnf {self.max_var} {len(self.clauses)}\n")
            for clause in self.clauses:
                handle.write(" ".join(map(str, clause)))
                handle.write(" 0\n")


@dataclass(frozen=True)
class EncodingMetadata:
    states: int
    type0_states: int
    sample_indices: Tuple[int, ...]
    words: Tuple[Word, ...]
    labels: Tuple[int, ...]
    trie: Trie
    x_vars: Mapping[Tuple[int, int], int]
    y_vars: Mapping[Tuple[int, int, int], int]
    output_vars: Mapping[Tuple[int, int], int]
    variables: Mapping[Tuple[object, ...], int]
    anchors: Mapping[str, Tuple[int, ...]]


def allowed_colors(states: int, type0_states: int, node_type: int) -> range:
    return range(0, type0_states) if node_type == 0 else range(type0_states, states)


def build_exact_cnf(
    sample_indices: Sequence[int],
    states: int,
    type0_states: int,
    *,
    base: int = 4,
    add_anchor_symmetry: bool = True,
) -> Tuple[CNF, EncodingMetadata]:
    if not (1 <= type0_states < states):
        raise ValueError("need at least one state of each Zeckendorf type")
    words_list, labels_list = make_samples(base, sample_indices)
    trie = build_trie(words_list, labels_list)
    conflict = build_common_suffix_conflicts(words_list, labels_list, trie)
    cnf = CNF()

    x_vars: Dict[Tuple[int, int], int] = {}
    for node, typ in enumerate(trie.node_type):
        for color in allowed_colors(states, type0_states, typ):
            x_vars[(node, color)] = cnf.var("x", node, color)

    y_vars: Dict[Tuple[int, int, int], int] = {}
    for source in range(states):
        source_type = 0 if source < type0_states else 1
        for symbol in (0, 1):
            if source_type == 1 and symbol == 1:
                continue
            target_type = 0 if symbol == 0 else 1
            for target in allowed_colors(states, type0_states, target_type):
                y_vars[(source, symbol, target)] = cnf.var("y", source, symbol, target)

    output_bits = max(1, (base - 1).bit_length())
    output_vars: Dict[Tuple[int, int], int] = {}
    for color in range(states):
        for bit in range(output_bits):
            output_vars[(color, bit)] = cnf.var("output", color, bit)

    for node, typ in enumerate(trie.node_type):
        cnf.exactly_one_pairwise(
            [x_vars[(node, color)] for color in allowed_colors(states, type0_states, typ)]
        )

    for source in range(states):
        source_type = 0 if source < type0_states else 1
        for symbol in (0, 1):
            if source_type == 1 and symbol == 1:
                continue
            target_type = 0 if symbol == 0 else 1
            cnf.at_most_one_pairwise(
                [
                    y_vars[(source, symbol, target)]
                    for target in allowed_colors(states, type0_states, target_type)
                ]
            )

    for parent, symbol, child in trie.edges:
        parent_colors = allowed_colors(states, type0_states, trie.node_type[parent])
        child_colors = allowed_colors(states, type0_states, trie.node_type[child])
        for source in parent_colors:
            for target in child_colors:
                cnf.add(
                    -x_vars[(parent, source)],
                    -x_vars[(child, target)],
                    y_vars[(source, symbol, target)],
                )

    for node, label in trie.terminal.items():
        for color in allowed_colors(states, type0_states, trie.node_type[node]):
            x = x_vars[(node, color)]
            for bit in range(output_bits):
                output = output_vars[(color, bit)]
                cnf.add(-x, output if ((label >> bit) & 1) else -output)

    root = trie.node_id[()]
    cnf.add(x_vars[(root, 0)])
    cnf.add(y_vars[(0, 0, 0)])

    anchors: Dict[str, Tuple[int, ...]] = {}
    if add_anchor_symmetry:
        type0_triangle = triangle_containing(conflict, trie, root, 0)
        type1_triangle = triangle_containing(conflict, trie, None, 1)
        if type0_triangle is not None:
            if type0_states < 3:
                cnf.add()
            else:
                for node, color in zip(type0_triangle, range(3)):
                    cnf.add(x_vars[(node, color)])
                anchors["type0"] = type0_triangle
        if type1_triangle is not None:
            if states - type0_states < 3:
                cnf.add()
            else:
                for node, color in zip(
                    type1_triangle, range(type0_states, type0_states + 3)
                ):
                    cnf.add(x_vars[(node, color)])
                anchors["type1"] = type1_triangle

    metadata = EncodingMetadata(
        states=states,
        type0_states=type0_states,
        sample_indices=tuple(sample_indices),
        words=tuple(words_list),
        labels=tuple(labels_list),
        trie=trie,
        x_vars=x_vars,
        y_vars=y_vars,
        output_vars=output_vars,
        variables=dict(cnf.variables),
        anchors=anchors,
    )
    return cnf, metadata


def parse_cadical_model(output: str) -> Set[int]:
    true_variables: Set[int] = set()
    saw_model = False
    for line in output.splitlines():
        if line.startswith("v "):
            saw_model = True
            for token in line[2:].split():
                literal = int(token)
                if literal > 0:
                    true_variables.add(literal)
    if not saw_model:
        raise RuntimeError("SAT result contained no model lines")
    return true_variables


@dataclass
class Candidate:
    transitions: Dict[Tuple[int, int], int]
    outputs: Dict[int, int]


def decode_candidate(metadata: EncodingMetadata, true_variables: Set[int], base: int) -> Candidate:
    transitions: Dict[Tuple[int, int], int] = {}
    for key, variable in metadata.y_vars.items():
        if variable in true_variables:
            source, symbol, target = key
            old = transitions.get((source, symbol))
            if old is not None and old != target:
                raise AssertionError("model violates transition functionality")
            transitions[(source, symbol)] = target

    bits = max(1, (base - 1).bit_length())
    outputs: Dict[int, int] = {}
    for color in range(metadata.states):
        value = 0
        for bit in range(bits):
            if metadata.output_vars[(color, bit)] in true_variables:
                value |= 1 << bit
        outputs[color] = value
    return Candidate(transitions, outputs)


def candidate_output(candidate: Candidate, word: Word) -> Optional[int]:
    state = 0
    for symbol in word:
        state = candidate.transitions.get((state, symbol), -1)
        if state < 0:
            return None
    return candidate.outputs[state]


def validate_candidate(candidate: Candidate, base: int, limit: int) -> List[int]:
    failures: List[int] = []
    for index in range(limit):
        word = zeckendorf_word(base**index)
        expected = golden_digit(base, index)
        if candidate_output(candidate, word) != expected:
            failures.append(index)
    return failures


def run_cadical(
    solver: str, cnf_path: Path, timeout_seconds: int
) -> Tuple[str, str, float]:
    start = time.monotonic()
    try:
        process = subprocess.run(
            [solver, str(cnf_path)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired as error:
        elapsed = time.monotonic() - start
        partial = error.stdout.decode() if isinstance(error.stdout, bytes) else (error.stdout or "")
        return "TIMEOUT", partial, elapsed

    elapsed = time.monotonic() - start
    output = process.stdout
    if "s UNSATISFIABLE" in output or process.returncode == 20:
        return "UNSAT", output, elapsed
    if "s SATISFIABLE" in output or process.returncode == 10:
        return "SAT", output, elapsed
    return f"UNKNOWN_EXIT_{process.returncode}", output, elapsed


def run_cegis(args: argparse.Namespace) -> Dict[str, object]:
    selected = list(range(args.seed))
    selected_set = set(selected)
    history: List[Dict[str, object]] = []

    for round_index in range(args.max_rounds):
        with tempfile.TemporaryDirectory(prefix="phi-b4-") as temporary:
            cnf, metadata = build_exact_cnf(
                selected,
                args.states,
                args.type0_states,
                base=args.base,
                add_anchor_symmetry=not args.no_anchors,
            )
            cnf_path = Path(temporary) / "instance.cnf"
            cnf.write_dimacs(cnf_path)
            status, output, elapsed = run_cadical(
                args.solver, cnf_path, args.timeout
            )
            record: Dict[str, object] = {
                "round": round_index,
                "selected_count": len(selected),
                "selected_indices": list(selected),
                "variables": cnf.max_var,
                "clauses": len(cnf.clauses),
                "trie_nodes": len(metadata.trie.nodes),
                "status": status,
                "seconds": elapsed,
                "anchors": {key: list(value) for key, value in metadata.anchors.items()},
                "solver_tail": output.splitlines()[-30:],
            }
            history.append(record)
            print(json.dumps(record, sort_keys=True), flush=True)

            if status == "UNSAT":
                return {
                    "result": "UNSAT",
                    "meaning": (
                        "No typed zero-invariant partial DFAO with this state split "
                        "fits the selected finite sample, modulo the recorded anchor "
                        "renaming symmetry."
                    ),
                    "base": args.base,
                    "states": args.states,
                    "type0_states": args.type0_states,
                    "type1_states": args.states - args.type0_states,
                    "selected_indices": selected,
                    "history": history,
                }

            if status != "SAT":
                return {
                    "result": status,
                    "base": args.base,
                    "states": args.states,
                    "type0_states": args.type0_states,
                    "type1_states": args.states - args.type0_states,
                    "selected_indices": selected,
                    "history": history,
                }

            true_variables = parse_cadical_model(output)
            candidate = decode_candidate(metadata, true_variables, args.base)
            failures = validate_candidate(candidate, args.base, args.validation)
            record["validation_failures"] = failures[:100]
            record["validation_failure_count"] = len(failures)
            if not failures:
                return {
                    "result": "SAT_VALIDATED",
                    "meaning": (
                        "A candidate with this fixed state-type split fits every "
                        "tested index. This is finite computational evidence only."
                    ),
                    "base": args.base,
                    "states": args.states,
                    "type0_states": args.type0_states,
                    "type1_states": args.states - args.type0_states,
                    "selected_indices": selected,
                    "validated_range": [0, args.validation],
                    "candidate": {
                        "transitions": [
                            [source, symbol, target]
                            for (source, symbol), target in sorted(candidate.transitions.items())
                        ],
                        "outputs": [candidate.outputs[state] for state in range(args.states)],
                    },
                    "history": history,
                }

            additions = [index for index in failures if index not in selected_set][
                : args.batch
            ]
            if not additions:
                return {
                    "result": "SAT_STALLED",
                    "base": args.base,
                    "states": args.states,
                    "type0_states": args.type0_states,
                    "type1_states": args.states - args.type0_states,
                    "selected_indices": selected,
                    "history": history,
                }
            selected.extend(additions)
            selected.sort()
            selected_set.update(additions)

    return {
        "result": "ROUND_LIMIT",
        "base": args.base,
        "states": args.states,
        "type0_states": args.type0_states,
        "type1_states": args.states - args.type0_states,
        "selected_indices": selected,
        "history": history,
    }


def analyze_graph(base: int, sample_count: int) -> Dict[str, object]:
    indices = list(range(sample_count))
    words, labels = make_samples(base, indices)
    trie = build_trie(words, labels)
    conflict = build_common_suffix_conflicts(words, labels, trie)
    edges = sum(len(neighbours) for neighbours in conflict.adjacency) // 2
    active = sum(bool(neighbours) for neighbours in conflict.adjacency)
    type_counts = [
        sum(1 for typ in trie.node_type if typ == node_type) for node_type in (0, 1)
    ]
    type_edges = []
    for node_type in (0, 1):
        count = 0
        for left, neighbours in enumerate(conflict.adjacency):
            if trie.node_type[left] != node_type:
                continue
            count += sum(
                1
                for right in neighbours
                if right > left and trie.node_type[right] == node_type
            )
        type_edges.append(count)
    return {
        "base": base,
        "sample_count": sample_count,
        "trie_nodes": len(trie.nodes),
        "trie_edges": len(trie.edges),
        "conflict_edges": edges,
        "active_conflict_nodes": active,
        "type_nodes": type_counts,
        "type_internal_conflict_edges": type_edges,
        "type0_anchor_triangle": triangle_containing(
            conflict, trie, trie.node_id[()], 0
        ),
        "type1_anchor_triangle": triangle_containing(conflict, trie, None, 1),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    analyze = subparsers.add_parser("analyze")
    analyze.add_argument("--base", type=int, default=4)
    analyze.add_argument("--samples", type=int, nargs="+", required=True)
    analyze.add_argument("--output", type=Path)

    cegis = subparsers.add_parser("cegis")
    cegis.add_argument("--base", type=int, default=4)
    cegis.add_argument("--states", type=int, required=True)
    cegis.add_argument("--type0-states", type=int, required=True)
    cegis.add_argument("--seed", type=int, default=79)
    cegis.add_argument("--validation", type=int, default=200)
    cegis.add_argument("--batch", type=int, default=8)
    cegis.add_argument("--max-rounds", type=int, default=20)
    cegis.add_argument("--timeout", type=int, default=900)
    cegis.add_argument("--solver", default="cadical")
    cegis.add_argument("--no-anchors", action="store_true")
    cegis.add_argument("--output", type=Path, required=True)

    args = parser.parse_args()
    if args.command == "analyze":
        result = [analyze_graph(args.base, count) for count in args.samples]
        text = json.dumps(result, indent=2, sort_keys=True)
        print(text)
        if args.output:
            args.output.write_text(text + "\n", encoding="utf-8")
        return 0

    result = run_cegis(args)
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
