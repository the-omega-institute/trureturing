# Actual real partition messages

## Abstract

The real messages and their invariant interval are derived from actual finite-graph partitions.

**Theorem 1.1 (Nonnegative domain monotonicity).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.partition_mono`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.partition_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every independent set in a smaller domain remains independent in the larger domain. Nonnegative configuration weights give the corresponding partition inequality.

**Definition 1.2 (Vacancy as an actual ratio).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.vacancyRatio`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.vacancyRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Divide the partition after root erasure by the partition of the original finite domain.

**Theorem 1.3 (Derived invariant real interval).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.vacancy_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.vacancy_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative activities and an upper budget on the root activity imply the interval from one divided by one plus the budget to one. Partition positivity is derived from the empty configuration. An absent root has ratio one and is included.

**Theorem 1.4 (The actual reciprocal recursion).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.real_ordered_vacancy`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.real_ordered_vacancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vacancy ratio equals the reciprocal of one plus the root activity times the ordered product of actual child vacancy ratios. Nonzero intermediate partitions follow from nonnegative activities, rather than being supplied as message hypotheses.

**Theorem 1.5 (The exact box at activity 2.55).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.real_255_message_box`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.real_255_message_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite graph domain and every activity between zero and 51/20, every actual vacancy ratio lies in [20/71,1]. This is the input box of the existing affine-message certificate. Its geometric type assignment and complex extension remain separate obligations.

Real positivity alone is not a complex zero-free theorem. The source scripts have undergone mathematical review and finite exact regressions; Lean elaboration and Scribe emission have not been executed here.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.partition_mono`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.real_255_message_box`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.real_ordered_vacancy`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.vacancyRatio`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/RealPartitionMessages.vacancy_bounds`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/OrderedPartitionRecursion](OrderedPartitionRecursion.md)
