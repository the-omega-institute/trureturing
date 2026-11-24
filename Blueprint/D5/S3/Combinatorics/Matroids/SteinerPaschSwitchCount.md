# Pasch configurations and fixed-pivot switch counts

## Abstract

Pasch configurations detect whether the number of successful starts can vary with the labels.

**Theorem 1.1 (An opposite pair in a Pasch gives variable switch counts).**

Lean statement: `D5/S3/Combinatorics/Matroids/SteinerPaschSwitchCount.variableLabelledSwitchCount_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/SteinerPaschSwitchCount.variableLabelledSwitchCount_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Giovanni Falcone, Ágota Figula, Mario Galici (2025). *Extensions of Steiner Triple Systems*. DOI: [10.1002/jcd.21964](https://doi.org/10.1002/jcd.21964). URL: <https://arxiv.org/abs/2406.12796>.

*Commentary.*

Fix two distinct pivots in a finite Steiner loop with trivial centre and fix a finite nontrivial binary fibre. Use the graph given by left multiplication by the pivots. In normalized extensions, the compatible labelled complete triple systems give at least two distinct successful-start counts exactly when four blocks form a Pasch in which the two pivots occur in no common block.

The four other points of such a Pasch form a square in the graph of the two matchings. Uniqueness of the block through two points excludes the special square containing the identity. Conversely, each other square gives four blocks through the two pivots and four distinct corners. The count range gives two distinct values as soon as there is one such square.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/SteinerPaschSwitchCount.variableLabelledSwitchCount_iff`
- Dependency: [D5/S3/Combinatorics/Matroids/SteinerFixedPivotCountRange](SteinerFixedPivotCountRange.md)
