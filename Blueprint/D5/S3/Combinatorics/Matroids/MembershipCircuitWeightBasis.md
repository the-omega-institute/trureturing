# Weight Coordinates from Petal Membership

## Abstract

An integral basis distinguishes petals on their zero-weight coordinates.

**Theorem 1.1 (A simultaneous supported basis).**

Lean statement: `D5/S3/Combinatorics/Matroids/MembershipCircuitWeightBasis.exists_membership_separating_weight_basis`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/MembershipCircuitWeightBasis.exists_membership_separating_weight_basis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Keep a pivot outside every petal. Partition the other indices by identical membership in the petals. A supported integral basis concentrates the weights at one index of each class, preserves each petal span in both directions, and preserves the pivot line. If every pair of petals differs on a class of size at least two, the petals have distinct intersections with the zero-weight indices outside the pivot.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/MembershipCircuitWeightBasis.exists_membership_separating_weight_basis`
- Dependency: [D5/S3/Combinatorics/Matroids/CircuitWeightBlocks](CircuitWeightBlocks.md)
