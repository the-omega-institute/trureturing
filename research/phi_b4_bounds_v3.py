#!/usr/bin/env python3
"""Exact-state strengthened search for the typed golden-ratio base-4 DFAO bound.

This layer starts from the sound RGS encoder in ``phi_b4_bounds_v2`` and adds:

* every color must occur on the finite prefix trie, so the formula represents
  an exact reachable state count rather than an at-most budget with unused
  colors;
* explicit transition-to-child propagation clauses, which are logically
  redundant but substantially strengthen unit propagation.

For a global lower bound, exact-state refutations must be accumulated over all
smaller state counts. The public <=14 result supplies the preceding boundary;
this experiment targets the previously open exact 15-state layer.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence, Tuple

import phi_b4_bounds as core
import phi_b4_bounds_v2 as v2


_original_build = v2.build_strong_cnf


def build_exact_used_cnf(
    sample_indices: Sequence[int],
    states: int,
    type0_states: int,
    *,
    base: int = 4,
) -> Tuple[core.CNF, v2.StrongMetadata]:
    cnf, metadata = _original_build(
        sample_indices,
        states,
        type0_states,
        base=base,
    )

    # Restricted-growth ``seen`` variables already express whether a color has
    # appeared by a given prefix position. Requiring the final one for every
    # color makes every named state reachable on the sample trie.
    for node_type in (0, 1):
        nodes = [
            node
            for node, typ in enumerate(metadata.trie.node_type)
            if typ == node_type
        ]
        if not nodes:
            cnf.add()
            continue
        last_position = len(nodes) - 1
        for color in v2.color_range(states, type0_states, node_type):
            cnf.add(metadata.seen_vars[(node_type, last_position, color)])

    # If a transition q -a-> r is selected and a trie node of color q has an
    # a-child, that child must have color r. These clauses are consequences of
    # the forward edge clauses plus transition functionality, and are added
    # solely to improve propagation.
    for parent, symbol, child in metadata.trie.edges:
        parent_colors = v2.color_range(
            states, type0_states, metadata.trie.node_type[parent]
        )
        child_colors = list(
            v2.color_range(
                states, type0_states, metadata.trie.node_type[child]
            )
        )
        for source in parent_colors:
            cnf.add(
                -metadata.x_vars[(parent, source)],
                *[
                    metadata.y_vars[(source, symbol, target)]
                    for target in child_colors
                ],
            )
            for target in child_colors:
                cnf.add(
                    -metadata.x_vars[(parent, source)],
                    -metadata.y_vars[(source, symbol, target)],
                    metadata.x_vars[(child, target)],
                )

    return cnf, metadata


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", type=int, default=4)
    parser.add_argument("--states", type=int, required=True)
    parser.add_argument("--type0-states", type=int, required=True)
    parser.add_argument("--seed", type=int, default=79)
    parser.add_argument("--validation", type=int, default=1000)
    parser.add_argument("--batch", type=int, default=4)
    parser.add_argument("--max-rounds", type=int, default=10)
    parser.add_argument("--timeout", type=int, default=900)
    parser.add_argument("--solver", default="cadical")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    v2.build_strong_cnf = build_exact_used_cnf
    result = v2.run_cegis(args)
    result["encoder"] = "exact-used-rgs-v3"
    result["all_colors_used"] = True
    result["claim_boundary"] = (
        "UNSAT excludes this exact reachable state count and fixed type split. "
        "A <=k lower bound additionally requires exact refutations for every "
        "smaller state count or a separate at-most encoding."
    )
    args.output.write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
