# A gap in Laurent direction types

## Abstract

Connectedness restricts the possible numbers of distinct Laurent direction triples.

**Theorem 1.1 (Four and six direction triples are impossible).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes.card_directionTypes_le_three_or_eq_five_or_ge_seven`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes.card_directionTypes_le_three_or_eq_five_or_ge_seven` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A two-step walk preserves the direction triple of its middle vertex. Thus a change of neighbor partition along the walk gives two distinct partitions sharing a block. Their union has five triples. The two different splits of the complementary six axes force any third partition to contribute at least two new triples.

**Theorem 1.2 (Five triples force a common direction block).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes.two_partitions_of_five_directionTypes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes.two_partitions_of_five_directionTypes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exactly five triples leave two realized neighbor partitions. They share one block. Deleting that block from a partition leaves a split of the complementary six coordinates into two triples.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes.card_directionTypes_le_three_or_eq_five_or_ge_seven`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Laurent/Q9LaurentDirectionTypes.two_partitions_of_five_directionTypes`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LaurentGainPartition](../Q9LaurentGainPartition.md)
