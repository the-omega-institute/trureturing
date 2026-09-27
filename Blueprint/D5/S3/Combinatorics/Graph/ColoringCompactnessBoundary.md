# The finite-palette boundary of coloring compactness

## Abstract

Finite palettes support graph-coloring compactness; an infinite palette need not.

**Theorem 1.1 (Finite compactness and its infinite-palette failure).**

Lean statement: `D5/S3/Combinatorics/Graph/ColoringCompactnessBoundary.finite_palette_compactness_and_infinite_palette_failure`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ColoringCompactnessBoundary.finite_palette_compactness_and_infinite_palette_failure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* N. G. de Bruijn and P. Erdos (1951). *A Colour Problem for Infinite Graphs and a Problem in the Theory of Relations*. DOI: [10.1016/S1385-7258(51)50053-7](https://doi.org/10.1016/S1385-7258(51)50053-7). URL: <https://doi.org/10.1016/S1385-7258(51)50053-7>.

*Commentary.*

For every simple graph G and natural number k, G has a proper coloring by Fin(k) exactly when each finite induced subgraph does. The reverse implication adapts induced-subgraph colorings to the finite-subgraph premise of Mathlib's pinned compactness theorem; it does not reproduce the compactness argument.

The same local-to-global statement fails when the palette is Nat. Every finite induced subgraph of the complete graph on Set(Nat) can be colored by enumerating its finite vertex subtype and embedding that finite index into Nat. Any global Nat-coloring would be injective, because all distinct vertices are adjacent, contradicting Cantor's theorem that no injection Set(Nat) to Nat exists. The finite and infinite clauses form one boundary statement; the source records the classical finite-palette theorem, while the explicit Cantor witness is repository-derived.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ColoringCompactnessBoundary.finite_palette_compactness_and_infinite_palette_failure`
