# Weight Coordinates from Private Pairs

## Abstract

An integral basis preserves overlapping faces and separates their coefficients.

**Theorem 1.1 (Separating zero-weight coordinates).**

Lean statement: `D5/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis.exists_private_pair_weight_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis.exists_private_pair_weight_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the coordinate indices form a finite set and carry positive integer weights. Fix a pivot outside every indexed face. Suppose each face contains two distinct indices that are in no other face. Partition the indices by membership in the faces and by equality to the pivot. An integral change of basis concentrates the weights on one index per block and preserves each face span in both directions. The pivot line is preserved. Each private pair lies in one block, so at least one of its two indices has zero new weight. The set of zero-weight indices outside the pivot therefore meets distinct faces in distinct subsets.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/PrivatePairCircuitWeightBasis.exists_private_pair_weight_basis`
- Dependency: [D5/S3/Combinatorics/Matroids/MembershipCircuitWeightBasis](MembershipCircuitWeightBasis.md)
