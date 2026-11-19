# Independent subsets of a graph join

## Abstract

Independent subsets of a graph join lie entirely on one side.

**Definition 1.1 (Join of two graphs).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.join`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.join` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertex domain is the tagged disjoint sum of the two original domains. Every cross edge is present. Each induced graph retains precisely its original edges. Equivalently, take the complement of the disjoint sum of the two complements.

**Theorem 1.2 (Complete configuration classification).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.configurations_join`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.configurations_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite vertex subsets V and W, the independent subsets of their join are the union of the embedded independent subsets on V and on W. An independent subset containing a left vertex cannot contain a right vertex. Both embedded families contain the empty subset, and their intersection contains nothing else.

**Theorem 1.3 (Partition sum with one empty subset).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.partition_join`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.partition_join` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any activity z in a commutative ring, the native partition sum of the join is the sum of the two native partition sums minus one. Subtracting one corrects the repeated empty subset. This holds for integer polynomials and for complex activities, with no nonzero or positivity hypothesis.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.configurations_join`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.join`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/PartitionJoin.partition_join`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](IndependentPartitionDeletion.md)
