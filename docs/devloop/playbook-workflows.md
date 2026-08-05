# Repository workflow playbook

The executable source of truth is `make help`. This page names the workflow entrypoints;
it does not duplicate their command sequences.

## Theorem delivery

Run `make deliver-check BASE=origin/dev` after the Lean declaration and its Blueprint
mirror are ready. The target derives receipts before freezing, freezes after every other
mutating derivation, and then runs the read-only emission, digestion, and preflight gates.
Keep the resulting freeze event in the same commit and PR as the theorem it attests.

## Two-stage receipts

The capability or theorem PR derives its stored state from its own base and may remain
partial. After that PR lands, the closure PR starts from the shared base and runs
`make receipts-stage BASE=origin/dev` before claiming absorption. A newly absorbed atom
with explicit multiple clauses must first be decomposed; an empty
`unresolved_subitems` list is rejected for that transition.

## Derived refresh

For a BEHIND branch or a base-advance race, run
`make derived-refresh BASE=origin/dev`. It merges the selected base, rebuilds the Lean
report, and recomputes and checks derived artifacts through their canonical producers.

Do not translate these targets into copied shell snippets in issues or review notes. If
the sequence changes, change the canonical script and its integration tests.
