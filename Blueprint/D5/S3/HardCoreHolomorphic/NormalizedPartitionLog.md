# NormalizedPartitionLog

## Abstract

Branch-correct normalized logarithms of actual finite-grid partitions.

**Definition 1.1 (orderedLog).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.orderedLog`

*Formalization.* `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.orderedLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum principal logs of the actual successive deletion ratios. The list may be partial or contain repeated/absent vertices; those cases are not silently discarded.

**Theorem 1.2 (ordered log perm).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_perm`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_perm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Local square flatness proves exact order independence by adjacent swaps. This does not identify the total sum with the principal logarithm of the full partition.

**Theorem 1.3 (ordered log exp).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_exp`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exponentiation telescopes to the exact quotient for an arbitrary deletion list. Nonzero denominators are derived from the established common grid tube.

**Theorem 1.4 (ordered log zero).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordered logs are normalized to zero at zero activity, without a branch choice based on a floating approximation.

**Theorem 1.5 (ordered log hasDerivAt).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete differential telescopes just like the partition products. This theorem covers arbitrary partial lists and all complex points in the tube.

**Definition 1.6 (normalizedLog).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalizedLog`

*Formalization.* `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalizedLog` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A canonical value chosen using the finite set's existing list enumeration. Its agreement with every complete distinct enumeration is proved below.

**Theorem 1.7 (complete order eq).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.complete_order_eq`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.complete_order_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every complete, repetition-free deletion list gives the same normalized value. Thus the choice of Finset.toList is not mathematical data of the result.

**Theorem 1.8 (normalized log exp).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_exp`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized logarithm exponentiates to the actual independent-set sum.

**Theorem 1.9 (normalized log zero).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_zero`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Canonical normalization at the activity-zero endpoint.

**Theorem 1.10 (normalized log hasDerivAt).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_hasDerivAt`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_hasDerivAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized branch has precisely the actual logarithmic derivative Z'/Z.

**Theorem 1.11 (normalized log differentiableOn).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_differentiableOn`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_differentiableOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Holomorphy on the original common activity neighborhood, with no new width or graph-dependent analytic-continuation premise.

**Theorem 1.12 (normalized log re).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_re`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_re` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual real part equals log of the actual partition modulus. Only the real part, not the full complex value, is identified with the principal log.

**Theorem 1.13 (normalized log im bound).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_im_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_im_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A volume-linear imaginary bound for the chosen analytic branch. This allows winding of the total partition while controlling it uniformly per vertex.

**Theorem 1.14 (normalized log delete).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_delete`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_delete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact canonical deletion recursion. The complete logarithm may accumulate phase, yet its one-vertex increment is always the local principal logarithm.

**Theorem 1.15 (normalized log volume bounds).**

Lean statement: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_volume_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_volume_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized finite-volume logarithm is bounded linearly in volume, with constants independent of the domain, its boundary and the deletion order.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.complete_order_eq`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalizedLog`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_delete`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_differentiableOn`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_exp`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_hasDerivAt`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_im_bound`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_re`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_volume_bounds`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.normalized_log_zero`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.orderedLog`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_exp`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_hasDerivAt`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_perm`
- Truth anchor: `D5/S3/HardCoreHolomorphic/NormalizedPartitionLog.ordered_log_zero`
- Dependency: [D5/S3/HardCoreHolomorphic/PartitionLogCocycle](PartitionLogCocycle.md)
