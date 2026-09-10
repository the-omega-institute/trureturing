# Ordered partition recursion

## Abstract

Ordered elimination is derived from actual independent-set partitions, retaining all intermediate domains.

**Definition 1.1 (Successive actual vertex deletions).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each listed vertex is erased from the current finite domain before continuing.

**Definition 1.2 (Vacant numerator factors).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.numeratorProduct`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.numeratorProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each factor is the independent-set partition after the next vertex deletion.

**Definition 1.3 (Pre-deletion denominator factors).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.denominatorProduct`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.denominatorProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each factor is the independent-set partition before the next deletion. These are actual proper domains when elimination begins after removing the root.

**Definition 1.4 (Ordered product of actual vacancy ratios).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.vacancyProduct`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.vacancyProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product retains the successive intermediate subgraphs. Later ratio identities explicitly discharge the nonzero denominator obligations.

**Theorem 1.5 (Final-domain set identity).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases_eq_sdiff`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases_eq_sdiff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The final domain equals the original domain minus the listed vertex set, including lists with repeated entries.

**Theorem 1.6 (Telescoping without division).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.telescoping_cross`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.telescoping_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The starting partition times the numerator product equals the ending partition times the denominator product. The semiring identity remains valid when any factor vanishes.

**Theorem 1.7 (Actual closed-neighborhood domain).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases_neighbors`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases_neighbors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the list represents exactly the root neighbors in the original domain, erasing that list after the root gives the closed-complement domain.

**Theorem 1.8 (The polynomial recurrence at every activity).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.ordered_partition_cross`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.ordered_partition_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combine the actual configuration deletion identity with denominator-free telescoping. No nonvanishing assumption is used, so complex zeros do not invalidate the identity.

**Theorem 1.9 (Derived ratio recursion on proper domains).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.partition_ordered_recursion`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.partition_ordered_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonzero partitions are required only for subsets of the domain after root deletion. The root partition is excluded from the premises. Exact factor cancellation then identifies the familiar hard-core recurrence.

**Theorem 1.10 (Noncircular nonvanishing propagation).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.partition_nonzero_of_local_denominator`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.partition_nonzero_of_local_denominator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Smaller-domain nonvanishing and a nonzero local recursion denominator imply that the original independent-set partition is nonzero. A later complex message-domain theorem must establish the local denominator condition.

These are classical elimination identities on the source-owned independent-set sum. The proof scripts are logically reviewed candidates, with no executed Lean or Scribe compilation claimed.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases_eq_sdiff`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.afterErases_neighbors`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.denominatorProduct`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.numeratorProduct`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.ordered_partition_cross`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.partition_nonzero_of_local_denominator`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.partition_ordered_recursion`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.telescoping_cross`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion.vacancyProduct`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](IndependentPartitionDeletion.md)
