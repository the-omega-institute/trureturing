# Pasch configurations and fixed-pivot switch counts

## Abstract

Pasch configurations detect whether the number of successful starts can vary with the labels.

**Theorem 1.1 (An opposite pair in a Pasch gives variable switch counts).**

Lean statement: `D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschSwitchCount.variableLabelledSwitchCount_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschSwitchCount.variableLabelledSwitchCount_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Fix distinct nonidentity pivots p and q in a finite Steiner loop with trivial centre, and fix a finite nontrivial binary fibre. Across normalized label tables, the compatible labelled extensions attain at least two successful-start counts for the lifted pivots (p,0) and (q,0) exactly when the original Steiner triple system contains a Pasch whose four blocks place p and q opposite one another.

The four other points of such a Pasch form a square in the graph of the two matchings. Uniqueness of the block through two points excludes the special square containing the identity. Conversely, each other square gives four blocks through the two pivots and four distinct corners. The count range gives two distinct values as soon as there is one such square.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/Steiner/SteinerPaschSwitchCount.variableLabelledSwitchCount_iff`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerFixedPivotCountRange](../SteinerFixedPivotCountRange.md)
