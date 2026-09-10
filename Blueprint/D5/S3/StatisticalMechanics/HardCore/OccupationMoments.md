# OccupationMoments

## Abstract

Actual occupation, normalized Gibbs probabilities and analytic response.

**Theorem 1.1 (configurations erase eq filter).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.configurations_erase_eq_filter`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.configurations_erase_eq_filter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual configurations omitting a vertex are exactly those on the erased vertex domain. The marked vertex need not belong to the domain.

**Theorem 1.2 (occupied weight add erased).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.occupied_weight_add_erased`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.occupied_weight_add_erased` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition the full configuration weight by actual root occupancy, before any division. This semiring identity also holds at zeros of a partition.

**Theorem 1.3 (weighted cardinality eq marked sum).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.weighted_cardinality_eq_marked_sum`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.weighted_cardinality_eq_marked_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Count each weighted independent configuration once per occupied vertex. This is an exact finite double-counting identity; no independence of vertex indicators is assumed.

**Theorem 1.4 (weighted cardinality eq partition differences).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.weighted_cardinality_eq_partition_differences`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.weighted_cardinality_eq_partition_differences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first weighted cardinality sum equals the sum of actual deletion partition differences. The identity is over every commutative ring.

**Definition 1.5 (moment).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment`

*Formalization.* `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Unnormalized occupation moment on the original configuration family. Order zero is the existing partition; no replacement graph model is introduced.

**Theorem 1.6 (moment zero order).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_zero_order`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_zero_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zeroth moment is exactly the existing constant-activity partition.

**Theorem 1.7 (moment one eq deletions).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_one_eq_deletions`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_one_eq_deletions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first moment has a local-deletion expression at every activity, including activity zero and partition zeros.

**Theorem 1.8 (moment succ at zero).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_succ_at_zero`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_succ_at_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive-order occupation moment vanishes at zero activity.

**Theorem 1.9 (moment hasDerivAt).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Direct termwise differentiation of the actual finite configuration sum. The natural predecessor in the exponent is harmless at the empty configuration.

**Theorem 1.10 (euler moment).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.euler_moment`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.euler_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Euler differentiation raises the occupation moment order. No division by activity or nonzero-activity assumption occurs, for any order k.

**Theorem 1.11 (partition euler occupation).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.partition_euler_occupation`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.partition_euler_occupation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The targeted observable identity for every finite domain of every simple graph. It holds over the real or complex numbers even at a partition zero.

**Theorem 1.12 (normalized moment response).**

Lean statement: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.normalized_moment_response`

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.normalized_moment_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Normalized moments satisfy a covariance-type response hierarchy wherever the actual partition is nonzero. Activity zero is retained in this formula.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.configurations_erase_eq_filter`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.euler_moment`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_hasDerivAt`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_one_eq_deletions`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_succ_at_zero`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.moment_zero_order`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.normalized_moment_response`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.occupied_weight_add_erased`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.partition_euler_occupation`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.weighted_cardinality_eq_marked_sum`
- Truth anchor: `D5/S3/StatisticalMechanics/HardCore/OccupationMoments.weighted_cardinality_eq_partition_differences`
- Dependency: [D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion](IndependentPartitionDeletion.md)
