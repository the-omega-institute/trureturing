# OccupationResponse

## Abstract

Actual occupation, normalized Gibbs probabilities and analytic response.

**Theorem 1.1 (grid partition occupation identity).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationResponse.grid_partition_occupation_identity`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationResponse.grid_partition_occupation_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact entire-plane occupation identity for the original square-grid sum. No nonvanishing or probability interpretation is needed for this equation.

**Theorem 1.2 (normalized log first moment).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_first_moment`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_first_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized logarithm's scaled derivative is the actual first moment normalized by the actual partition. The z=0 endpoint is included.

**Theorem 1.3 (normalized log occupation identity).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_occupation_identity`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_occupation_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual analytic response equals the sum of actual one-vertex occupied ratios. General complex values are analytic quantities, not probabilities.

**Theorem 1.4 (normalized log scaled response bound).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_scaled_response_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_scaled_response_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A graph-size-linear bound on the complex scaled response, using the previous actual marked-vacancy bound and preserving the same common tube.

**Theorem 1.5 (real Gibbs log derivative).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationResponse.real_gibbs_log_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationResponse.real_gibbs_log_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real Gibbs mean is exactly the scaled derivative of the already-owned normalized complex log at the same real activity. No derivative transport or unspecified probabilistic model is assumed.

**Theorem 1.6 (Gibbs expected card is log response).**

Lean statement: `D5/S3/HardCoreHolomorphic/OccupationResponse.gibbs_expected_card_is_log_response`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/OccupationResponse.gibbs_expected_card_is_log_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A direct finite-PMF expectation statement at the analytic endpoint. This binds the claimed physical observable to the actual sampled configurations.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationResponse.gibbs_expected_card_is_log_response`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationResponse.grid_partition_occupation_identity`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_first_moment`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_occupation_identity`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationResponse.normalized_log_scaled_response_bound`
- Truth anchor: `D5/S3/HardCoreHolomorphic/OccupationResponse.real_gibbs_log_derivative`
- Dependency: [D5/S3/HardCoreHolomorphic/NormalizedPartitionLog](NormalizedPartitionLog.md)
- Dependency: [D5/S3/StatisticalMechanics/HardCore/GibbsOccupation](../StatisticalMechanics/HardCore/GibbsOccupation.md)
