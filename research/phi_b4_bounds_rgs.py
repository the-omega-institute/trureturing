#!/usr/bin/env python3
"""Exact typed golden-ratio DFAO search with certified first-use symmetry.

For each Zeckendorf state type separately, colors are renamed by the order of
their first occurrence in the canonical unique-prefix trie. Every finite model
has exactly one such renaming after unused colors are placed last. The added
restricted-growth constraints therefore preserve satisfiability while removing
the independent state-permutation groups within the two types.
"""

from __future__ import annotations

import argparse
import json
import tempfile
from pathlib import Path
from typing import Dict, List

import phi_b4_bounds as core


def add_first_use_symmetry(
    cnf: core.CNF, metadata: core.EncodingMetadata
) -> Dict[str, object]:
    counts: Dict[str, object] = {}
    for node_type in (0, 1):
        nodes = [
            node
            for node, typ in enumerate(metadata.trie.node_type)
            if typ == node_type
        ]
        colors = list(
            core.allowed_colors(
                metadata.states, metadata.type0_states, node_type
            )
        )
        before_vars: Dict[tuple[int, int], int] = {}

        def before(position: int, local_color: int) -> int:
            key = (position, local_color)
            variable = before_vars.get(key)
            if variable is None:
                variable = cnf.var(
                    "rgs-before", node_type, position, local_color
                )
                before_vars[key] = variable
            return variable

        for local_color in range(len(colors)):
            cnf.add(-before(0, local_color))

        for position, node in enumerate(nodes):
            for local_color, color in enumerate(colors):
                old = before(position, local_color)
                new = before(position + 1, local_color)
                x = metadata.x_vars[(node, color)]
                # new <-> old or x
                cnf.add(-old, new)
                cnf.add(-x, new)
                cnf.add(-new, old, x)
                # A color may first appear only after its predecessor appeared.
                if local_color > 0:
                    cnf.add(-x, before(position, local_color - 1))

        counts[f"type{node_type}_nodes"] = len(nodes)
        counts[f"type{node_type}_colors"] = len(colors)
        counts[f"type{node_type}_symmetry_vars"] = len(before_vars)
    return counts


def run_cegis(args: argparse.Namespace) -> Dict[str, object]:
    selected = list(range(args.seed))
    selected_set = set(selected)
    history: List[Dict[str, object]] = []

    for round_index in range(args.max_rounds):
        with tempfile.TemporaryDirectory(prefix="phi-b4-rgs-") as temporary:
            cnf, metadata = core.build_exact_cnf(
                selected,
                args.states,
                args.type0_states,
                base=args.base,
                add_anchor_symmetry=False,
            )
            symmetry = add_first_use_symmetry(cnf, metadata)
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
                "status": status,
                "seconds": elapsed,
                "symmetry": symmetry,
                "solver_tail": output.splitlines()[-30:],
            }
            history.append(record)
            print(json.dumps(record, sort_keys=True), flush=True)

            if status == "UNSAT":
                return {
                    "result": "UNSAT",
                    "meaning": (
                        "No typed zero-invariant partial DFAO with this state "
                        "split fits the selected sample. First-use constraints "
                        "only choose the canonical representative of each "
                        "within-type state-renaming orbit."
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

            true_variables = core.parse_cadical_model(output)
            candidate = core.decode_candidate(
                metadata, true_variables, args.base
            )
            failures = core.validate_candidate(
                candidate, args.base, args.validation
            )
            record["validation_failures"] = failures[:100]
            record["validation_failure_count"] = len(failures)
            if not failures:
                return {
                    "result": "SAT_VALIDATED",
                    "meaning": (
                        "A candidate with this state-type split fits every "
                        "tested index. This remains finite computational "
                        "evidence until a global correctness proof is supplied."
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=int, default=4)
    parser.add_argument("--states", type=int, required=True)
    parser.add_argument("--type0-states", type=int, required=True)
    parser.add_argument("--seed", type=int, default=79)
    parser.add_argument("--validation", type=int, default=200)
    parser.add_argument("--batch", type=int, default=8)
    parser.add_argument("--max-rounds", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=600)
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
