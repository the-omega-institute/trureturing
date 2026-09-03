#!/usr/bin/env python3
"""Strengthened exact search for the typed golden-ratio base-4 DFAO bound.

This second research encoder adds two semantics-preserving accelerators:

1. Every common-suffix conflict is emitted explicitly as a color exclusion.
2. Colors inside each Zeckendorf state type obey a restricted-growth order,
   eliminating state-renaming symmetry while retaining unused trailing colors.

The generated formula is still an exact finite-sample identification problem,
subject to the proof obligations recorded in the TrueTurning M-series lane.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Mapping, Sequence, Set, Tuple

import phi_b4_bounds as core

Word = core.Word


@dataclass(frozen=True)
class StrongMetadata:
    states: int
    type0_states: int
    sample_indices: Tuple[int, ...]
    words: Tuple[Word, ...]
    labels: Tuple[int, ...]
    trie: core.Trie
    x_vars: Mapping[Tuple[int, int], int]
    y_vars: Mapping[Tuple[int, int, int], int]
    seen_vars: Mapping[Tuple[int, int, int], int]
    conflict_count: int


def color_range(states: int, type0_states: int, node_type: int) -> range:
    if node_type == 0:
        return range(type0_states)
    return range(type0_states, states)


def add_restricted_growth_symmetry(
    cnf: core.CNF,
    trie: core.Trie,
    x_vars: Mapping[Tuple[int, int], int],
    states: int,
    type0_states: int,
) -> Dict[Tuple[int, int, int], int]:
    """Canonicalize colors by order of first prefix occurrence within each type."""

    seen_vars: Dict[Tuple[int, int, int], int] = {}
    for node_type in (0, 1):
        nodes = [
            node
            for node, typ in enumerate(trie.node_type)
            if typ == node_type
        ]
        colors = list(color_range(states, type0_states, node_type))
        for position, node in enumerate(nodes):
            for local_index, color in enumerate(colors):
                seen = cnf.var("seen", node_type, position, color)
                seen_vars[(node_type, position, color)] = seen
                x = x_vars[(node, color)]
                if position == 0:
                    cnf.add(-seen, x)
                    cnf.add(-x, seen)
                else:
                    previous = seen_vars[(node_type, position - 1, color)]
                    cnf.add(-previous, seen)
                    cnf.add(-x, seen)
                    cnf.add(-seen, previous, x)

                if local_index > 0:
                    if position == 0:
                        cnf.add(-x)
                    else:
                        predecessor = colors[local_index - 1]
                        cnf.add(
                            -x,
                            seen_vars[
                                (node_type, position - 1, predecessor)
                            ],
                        )
    return seen_vars


def build_strong_cnf(
    sample_indices: Sequence[int],
    states: int,
    type0_states: int,
    *,
    base: int = 4,
) -> Tuple[core.CNF, StrongMetadata]:
    if not (1 <= type0_states < states):
        raise ValueError("need at least one state of each Zeckendorf type")

    words_list, labels_list = core.make_samples(base, sample_indices)
    trie = core.build_trie(words_list, labels_list)
    conflict = core.build_common_suffix_conflicts(
        words_list, labels_list, trie
    )
    cnf = core.CNF()

    x_vars: Dict[Tuple[int, int], int] = {}
    for node, node_type in enumerate(trie.node_type):
        for color in color_range(states, type0_states, node_type):
            x_vars[(node, color)] = cnf.var("x", node, color)

    y_vars: Dict[Tuple[int, int, int], int] = {}
    for source in range(states):
        source_type = 0 if source < type0_states else 1
        for symbol in (0, 1):
            if source_type == 1 and symbol == 1:
                continue
            target_type = 0 if symbol == 0 else 1
            for target in color_range(
                states, type0_states, target_type
            ):
                y_vars[(source, symbol, target)] = cnf.var(
                    "y", source, symbol, target
                )

    for node, node_type in enumerate(trie.node_type):
        cnf.exactly_one_pairwise(
            [
                x_vars[(node, color)]
                for color in color_range(
                    states, type0_states, node_type
                )
            ]
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
                    for target in color_range(
                        states, type0_states, target_type
                    )
                ]
            )

    for parent, symbol, child in trie.edges:
        for source in color_range(
            states, type0_states, trie.node_type[parent]
        ):
            for target in color_range(
                states, type0_states, trie.node_type[child]
            ):
                cnf.add(
                    -x_vars[(parent, source)],
                    -x_vars[(child, target)],
                    y_vars[(source, symbol, target)],
                )

    conflict_count = 0
    for left, neighbours in enumerate(conflict.adjacency):
        for right in neighbours:
            if right <= left:
                continue
            if trie.node_type[left] != trie.node_type[right]:
                continue
            conflict_count += 1
            for color in color_range(
                states, type0_states, trie.node_type[left]
            ):
                cnf.add(
                    -x_vars[(left, color)],
                    -x_vars[(right, color)],
                )

    root = trie.node_id[()]
    cnf.add(x_vars[(root, 0)])
    cnf.add(y_vars[(0, 0, 0)])

    seen_vars = add_restricted_growth_symmetry(
        cnf, trie, x_vars, states, type0_states
    )

    return cnf, StrongMetadata(
        states=states,
        type0_states=type0_states,
        sample_indices=tuple(sample_indices),
        words=tuple(words_list),
        labels=tuple(labels_list),
        trie=trie,
        x_vars=x_vars,
        y_vars=y_vars,
        seen_vars=seen_vars,
        conflict_count=conflict_count,
    )


def decode_candidate(
    metadata: StrongMetadata, true_variables: Set[int]
) -> core.Candidate:
    transitions: Dict[Tuple[int, int], int] = {}
    for key, variable in metadata.y_vars.items():
        if variable in true_variables:
            source, symbol, target = key
            old = transitions.get((source, symbol))
            if old is not None and old != target:
                raise AssertionError(
                    "model violates transition functionality"
                )
            transitions[(source, symbol)] = target

    node_color: Dict[int, int] = {}
    for key, variable in metadata.x_vars.items():
        if variable in true_variables:
            node, color = key
            old = node_color.get(node)
            if old is not None and old != color:
                raise AssertionError("model gives a node two colors")
            node_color[node] = color

    outputs: Dict[int, int] = {
        color: 0 for color in range(metadata.states)
    }
    observed: Dict[int, int] = {}
    for node, label in metadata.trie.terminal.items():
        color = node_color[node]
        old = observed.get(color)
        if old is not None and old != label:
            raise AssertionError(
                "model merges contradictory terminal outputs"
            )
        observed[color] = label
    outputs.update(observed)
    return core.Candidate(transitions, outputs)


def run_cegis(args: argparse.Namespace) -> Dict[str, object]:
    selected = list(range(args.seed))
    selected_set = set(selected)
    history: List[Dict[str, object]] = []

    for round_index in range(args.max_rounds):
        with tempfile.TemporaryDirectory(
            prefix="phi-b4-strong-"
        ) as temporary:
            cnf, metadata = build_strong_cnf(
                selected,
                args.states,
                args.type0_states,
                base=args.base,
            )
            cnf_path = Path(temporary) / "instance.cnf"
            cnf.write_dimacs(cnf_path)
            status, output, elapsed = core.run_cadical(
                args.solver, cnf_path, args.timeout
            )
            record: Dict[str, object] = {
                "round": round_index,
                "selected_count": len(selected),
                "selected_indices": list(selected),
                "variables": cnf.max_var,
                "clauses": len(cnf.clauses),
                "trie_nodes": len(metadata.trie.nodes),
                "internal_conflicts": metadata.conflict_count,
                "status": status,
                "seconds": elapsed,
                "solver_tail": output.splitlines()[-30:],
            }
            history.append(record)
            print(json.dumps(record, sort_keys=True), flush=True)

            if status == "UNSAT":
                return {
                    "encoder": "strong-rgs-v2",
                    "result": "UNSAT",
                    "meaning": (
                        "No typed zero-invariant partial DFAO with this "
                        "state-type split fits the selected finite sample, "
                        "under the restricted-growth renaming normal form."
                    ),
                    "base": args.base,
                    "states": args.states,
                    "type0_states": args.type0_states,
                    "type1_states": (
                        args.states - args.type0_states
                    ),
                    "selected_indices": selected,
                    "history": history,
                }

            if status != "SAT":
                return {
                    "encoder": "strong-rgs-v2",
                    "result": status,
                    "base": args.base,
                    "states": args.states,
                    "type0_states": args.type0_states,
                    "type1_states": (
                        args.states - args.type0_states
                    ),
                    "selected_indices": selected,
                    "history": history,
                }

            true_variables = core.parse_cadical_model(output)
            candidate = decode_candidate(metadata, true_variables)
            failures = core.validate_candidate(
                candidate, args.base, args.validation
            )
            record["validation_failure_count"] = len(failures)
            record["validation_failures"] = failures[:100]

            if not failures:
                return {
                    "encoder": "strong-rgs-v2",
                    "result": "SAT_VALIDATED",
                    "meaning": (
                        "A candidate with this fixed type split fits all "
                        "tested indices. This is finite evidence, not a "
                        "global upper-bound proof."
                    ),
                    "base": args.base,
                    "states": args.states,
                    "type0_states": args.type0_states,
                    "type1_states": (
                        args.states - args.type0_states
                    ),
                    "selected_indices": selected,
                    "validated_range": [0, args.validation],
                    "candidate": {
                        "transitions": [
                            [source, symbol, target]
                            for (source, symbol), target in sorted(
                                candidate.transitions.items()
                            )
                        ],
                        "outputs": [
                            candidate.outputs[state]
                            for state in range(args.states)
                        ],
                    },
                    "history": history,
                }

            additions = [
                index
                for index in failures
                if index not in selected_set
            ][: args.batch]
            if not additions:
                return {
                    "encoder": "strong-rgs-v2",
                    "result": "SAT_STALLED",
                    "base": args.base,
                    "states": args.states,
                    "type0_states": args.type0_states,
                    "type1_states": (
                        args.states - args.type0_states
                    ),
                    "selected_indices": selected,
                    "history": history,
                }
            selected.extend(additions)
            selected.sort()
            selected_set.update(additions)

    return {
        "encoder": "strong-rgs-v2",
        "result": "ROUND_LIMIT",
        "base": args.base,
        "states": args.states,
        "type0_states": args.type0_states,
        "type1_states": args.states - args.type0_states,
        "selected_indices": selected,
        "history": history,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=int, default=4)
    parser.add_argument("--states", type=int, required=True)
    parser.add_argument("--type0-states", type=int, required=True)
    parser.add_argument("--seed", type=int, default=79)
    parser.add_argument("--validation", type=int, default=200)
    parser.add_argument("--batch", type=int, default=8)
    parser.add_argument("--max-rounds", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=1200)
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    result = run_cegis(args)
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
