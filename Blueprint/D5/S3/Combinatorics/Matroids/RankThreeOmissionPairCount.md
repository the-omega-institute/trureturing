# The Minimum Number of Rank-Three Omissions

## Abstract

For finite triple families with at most one triple per pair, the sizes of the ternary potential fibers determine how many pairs require coverage.

**Theorem 1.1 (The mixed-pair lower bound).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount.potential_fiber_pair_count_le`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount.potential_fiber_pair_count_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the normalized ternary potential space of a pair-unique family have dimension d. For any evaluation basis, write q for three to the power d and s for the size of its zero fiber. There are q times (q minus one) ordered pairs of distinct fiber labels, with s squared point pairs per label pair. Every such pair lies in a listed triple, and each triple offers six ordered pairs of positions.

**Theorem 1.2 (Lifted affine lines attain the bound).**

Lean statement: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount.exists_lifted_omission_family`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount.exists_lifted_omission_family` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive s, take the product of the d-dimensional ternary coordinate space and the cyclic group of order s. List triples with distinct first coordinates and zero sum in the product. Each mixed pair determines its unique third point by the negative-sum rule. Same-fiber pairs force the normalized potentials to be constant on rows. The coordinate functions are independent potentials, while surjectivity of basis evaluation on the row labels bounds the potential dimension by d. All six ordered pairs of each listed triple are mixed, so the family meets the lower bound with equality.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount.exists_lifted_omission_family`
- Truth anchor: `D5/S3/Combinatorics/Matroids/RankThreeOmissionPairCount.potential_fiber_pair_count_le`
- Dependency: [D5/S3/Combinatorics/Matroids/RankThreeOmissionPotentialFibers](RankThreeOmissionPotentialFibers.md)
