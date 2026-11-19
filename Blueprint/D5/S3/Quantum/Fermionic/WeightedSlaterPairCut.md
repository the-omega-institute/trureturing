# Binary alternation rank for the weighted Slater marginal

## Abstract

The ordinary marginal rank for disjoint orbitals with two nonzero endpoint amplitudes.

**Theorem 1.1 (Rank with both endpoints available).**

Lean statement: `D5/S3/Quantum/Fermionic/WeightedSlaterPairCut.orderedMarginal_rank_of_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/WeightedSlaterPairCut.orderedMarginal_rank_of_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Split a finite linearly ordered site set into the retained side and its complement. Choose disjoint two-site pairs on each side, with the false endpoint earlier than the true endpoint. Assign an arbitrary nonzero complex amplitude to every endpoint. Form the ordered Slater cut matrix B using these columns in retained-first column order. No normalization of the amplitudes is required.

Let A be the binary matrix whose entries indicate whether the two pairs alternate in site order. The matrix B times its conjugate transpose has rank two to the power of the rank of A over the field with two elements. The row carrier includes all occupations. Empty pair lists and rank zero are included.

On occupations that choose one endpoint from each pair, the actual determinants give separate amplitude products and the binary character of the cross interaction. The character descends to the two images of the alternation matrix and its transpose. Normalize the separate amplitude vectors on each nonempty fiber to obtain the left and right isometries. Orthogonality of the image characters gives full rank on the image, and the positive fiber masses supply invertible row and column scalings. The supporting occupations embed isometrically into the full carrier.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/WeightedSlaterPairCut.orderedMarginal_rank_of_nonzero`
- Dependency: [D5/S3/Quantum/Fermionic/SlaterPairCutRank](SlaterPairCutRank.md)
