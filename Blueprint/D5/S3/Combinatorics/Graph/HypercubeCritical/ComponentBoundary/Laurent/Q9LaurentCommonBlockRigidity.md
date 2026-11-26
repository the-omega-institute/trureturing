# A shared direction triple forces a constant partition

## Abstract

A shared direction triple forces order fifty-four in a connected cubic Laurent component.

**Theorem 1.1 (Constant row partition and fifty-four vertices).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonBlockRigidity.constant_partition_and_card_eq_fiftyFour_of_common_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonBlockRigidity.constant_partition_and_card_eq_fiftyFour_of_common_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a connected induced cubic subgraph of the nine-cube satisfy a Laurent identity on one parity side. If one direction triple belongs to every row partition on that side, all those partitions agree and the subgraph has fifty-four vertices.

Deleting the common triple preserves each remaining component's partition, since two shared blocks determine all three. Its projected rows form a product of two three-point stars with a height inherited from the Laurent exponent. These products realize the balanced cut boxes in the shared-cut theorem. Hence the remaining two blocks agree up to exchange. The constant partition gives only three direction triples, excluding the seven-or-more alternative in the published order theorem.

This settles the common-triple case of the one-sided Laurent approach to Hong, Wu and Xia’s Problem 2. <https://arxiv.org/html/2610.09483v1#Thmproblem2>

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentCommonBlockRigidity.constant_partition_and_card_eq_fiftyFour_of_common_block`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentFiveTypeExclusion](Q9LaurentFiveTypeExclusion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentNormalizedBoxes](Q9LaurentNormalizedBoxes.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentSharedCutBoxes](Q9LaurentSharedCutBoxes.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentTransverseFibers](Q9LaurentTransverseFibers.md)
