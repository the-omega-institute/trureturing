# LinearVolumeVariance

## Abstract

Uniform complex response bounds control actual discrete Gibbs fluctuations.

**Definition 1.1 (complexMean).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complexMean`

*Formalization.* `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complexMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Analytic continuation of the actual mean particle number. The denominator is the zeroth moment, already proved equal to the actual partition.

**Definition 1.2 (varianceConstant).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.varianceConstant`

*Formalization.* `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.varianceConstant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One explicit sufficient variance coefficient, with no numerical sharpness claim. Its size comes from the inherited width epsilon = 10^-30.

**Theorem 1.3 (complex mean differentiableAt).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_differentiableAt`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_differentiableAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual mean continuation is holomorphic on the inherited common tube. Polynomial moments and the already-proved actual nonzero denominator suffice.

**Theorem 1.4 (complex mean eq log response).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_eq_log_response`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_eq_log_response` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Connect the same analytic mean to the existing normalized logarithm; there is no division by activity and the origin remains included.

**Theorem 1.5 (complex mean norm bound).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_norm_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_norm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual mean continuation has the inherited graph-size-linear norm bound.

**Theorem 1.6 (closed cauchy disk subset).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.closed_cauchy_disk_subset`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.closed_cauchy_disk_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed Cauchy disk stays strictly inside the common activity tube, including disks centered at either endpoint of the real interval.

**Theorem 1.7 (complex mean deriv bound).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_deriv_bound`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_deriv_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply Mathlib's Cauchy derivative estimate to the actual mean. The disk, its boundary bound, holomorphy and closed-disk continuity are all derived; no supplied Cauchy estimate or derivative bound is a theorem premise.

**Theorem 1.8 (variance eq scaled complex deriv).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.variance_eq_scaled_complex_deriv`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.variance_eq_scaled_complex_deriv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex derivative yields the actual real Gibbs variance. This uses both fields' identical finite moments and the already-proved response identity; no unproved interchange of real and complex derivatives is used.

**Theorem 1.9 (grid variance linear activity).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.grid_variance_linear_activity`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.grid_variance_linear_activity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sharper intermediate bound retains the real activity factor. In particular it vanishes at zero without a separate division-by-lambda step.

**Theorem 1.10 (grid variance linear volume).**

Lean statement: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.grid_variance_linear_volume`

*Proof.* Machine-checked in Lean as `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.grid_variance_linear_volume` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual finite-square-grid occupation variance grows at most linearly in volume, uniformly on the full closed interval [0,51/20]. The empty domain is included. The large explicit constant is sufficient, not sharp.

## References

- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.closed_cauchy_disk_subset`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complexMean`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_deriv_bound`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_differentiableAt`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_eq_log_response`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.complex_mean_norm_bound`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.grid_variance_linear_activity`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.grid_variance_linear_volume`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.varianceConstant`
- Truth anchor: `D5/S3/HardCoreHolomorphic/LinearVolumeVariance.variance_eq_scaled_complex_deriv`
- Dependency: [D5/S3/HardCoreHolomorphic/OccupationResponse](OccupationResponse.md)
