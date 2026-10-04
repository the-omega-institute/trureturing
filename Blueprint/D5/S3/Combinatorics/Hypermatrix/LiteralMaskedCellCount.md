# Exact cell cardinality

## Abstract

Exact cell cardinality

**Definition 1.1 (Literal masked-cell equations).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount.LiteralSolutions`

*Formalization.* `D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount.LiteralSolutions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

For each eligible or ineligible permutation pair sigma,pi, assign elements of F to the disjoint inversion coordinates. Require the actual product entries sum over b of cellA(r,b) cellB(b,j), using castSucc for the first face and succ for the second, to vanish at both original forbidden row thresholds.

**Theorem 1.2 (Exact cell cardinality).**

Lean statement: `D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount.literal_cell_count_original_masks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount.literal_cell_count_original_masks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Brandon Koprowski, Joel Brewster Lewis (2026). *Enumeration of Nondegenerate 2 x (k+1) x k Hypermatrices*. DOI: [10.48550/arXiv.2602.22129](https://doi.org/10.48550/arXiv.2602.22129). URL: <https://arxiv.org/abs/2602.22129v1>.

*Commentary.*

Let F be any finite field and k at least one. Let lambda and mu on Fin(k) be antitone, with mu(j) at most lambda(j), lambda(j) at most k minus j, and mu(j) strictly less than k minus j. For every permutation pair sigma of Fin(k plus one) and pi of Fin(k), the number of literal masked coordinate assignments is q to the natural value of the actual integer exponent E if the pair is Eligible at thresholds k plus one minus lambda and k plus one minus mu, and zero otherwise. Here q is the cardinality of F, and E is the existing inversion count minus the two actual forbidden counts. Each forbidden equation has a distinct coefficient-one final variable; an explicit acyclic order yields unique elimination and leaves exactly the free coordinates counted by the exponent. No specialized values are substituted for generic forbidden counts.

## References

- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount.LiteralSolutions`
- Truth anchor: `D5/S3/Combinatorics/Hypermatrix/LiteralMaskedCellCount.literal_cell_count_original_masks`
- Dependency: [D5/S3/Combinatorics/Hypermatrix/MaskedFacesDefs](MaskedFacesDefs.md)
