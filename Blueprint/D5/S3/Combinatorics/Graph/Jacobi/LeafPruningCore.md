# The greatest anchor-protected pruning core

## Abstract

The greatest anchor-protected pruning core

**Theorem 1.1 (Internal flag degree forces survival of every legal deletion chronology).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningCore.terminal_core_greatest`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningCore.terminal_core_greatest` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite actual flag graph and any genuine LeafPruning, every vertex set in which each nonanchor vertex has at least two incident flags whose mates lie in the set is contained in the terminal vertex set. Strong induction on deletion rank proves this: all earlier-deleted vertices have already been excluded from the proposed stable set, so two internal flags at a first alleged deletion would both remain present, contradicting deletion degree at most one. Protected anchors cannot be deleted. The statement counts actual flags, so a loop supplies two flags and parallel edges retain their multiplicity. It assumes neither connectedness nor positive genus and includes empty carriers.

The terminal set itself has the required degree property by terminal_degree. Apply the theorem to the terminal set of a second chronology, and then exchange the chronologies. Both inclusions give equality of the actual retained vertex sets. All anchors lie in that common set by protect_anchor, and the retained edges are precisely the original edges with both endpoints there. Thus the core is the greatest internally stable vertex set and is independent of deletion order. This proves the maximality and order-independence part of the source's pruned-hull construction; it does not prove degree-two suppression, skeleton insertion normal form, or the full four-loop vanishing theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/LeafPruningCore.terminal_core_greatest`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/FlagPruning](FlagPruning.md)
