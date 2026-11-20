# Cycle lifts, reversal classes and an added edge

## Abstract

The reversal quotient preserves actual undirected cycle completions and added-edge events.

**Theorem 1.1 (Reversal and the single-edge restriction).**

Lean statement: `D5/S3/Combinatorics/Graph/LinearForests/CycleLiftQuotient.reversal_quotient_and_added_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/LinearForests/CycleLiftQuotient.reversal_quotient_and_added_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite vertex set with at least three vertices and any simple graph on it. A lift orients exactly its edges and extends them by a whole-cycle permutation. The successor permutation fixes every prescribed edge orientation. Its two directions induce the actual undirected shadow.

The shadow map reaches every connected two-regular completion. Each fiber consists of an actual lift and its distinct reversal. Reversal is an involution, and the quotient sends each class to the same completion graph.

For distinct vertices, lifts with an added prescribed edge correspond to the original lifts whose shadow contains that edge. Restricting the orientations keeps the successor permutation, so it keeps the shadow and commutes with reversal. The inverse orients the added edge using the same successor. The argument covers a spanning path closed into a cycle and an edge already present.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/LinearForests/CycleLiftQuotient.reversal_quotient_and_added_edges`
- Dependency: [D5/S3/Combinatorics/Graph/LinearForests/UndirectedCycleCompletionLaw](UndirectedCycleCompletionLaw.md)
