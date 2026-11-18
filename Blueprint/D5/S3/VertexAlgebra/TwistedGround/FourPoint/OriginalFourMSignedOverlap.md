# Signed Four-Point Covariance and Mean

## Abstract

The actual signed external Gaussian on the native elliptic chart.

**Theorem 1.1 (Native covariance series).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_covariance_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_covariance_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the lattice Gram multiplier, the same-leg series is the signed J generator plus the native free block. The crossed series is minus the signed T generator in both leg orders. All sign pairs use the original complex radial domain.

**Theorem 1.2 (Native tagged matrix entry).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_tagged_entry`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_tagged_entry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two Taylor coefficients of this signed spatial generator recover the effective matrix entry at arbitrary original external labels, including repeated labels.

**Theorem 1.3 (Native mean in each mode).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_mean`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual charge pairing multiplies the signed source amplitude divided by the period. The left mean has a minus sign and the right mean has a plus sign.

**Theorem 1.4 (Native mean series).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_mean_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_mean_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Summing over modes yields the signed half-coordinate source times the negative charge pairing divided by the slit period.

**Theorem 1.5 (Elliptic spatial kernels).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_spatial_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_spatial_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same-leg mixed free block restores the Cauchy term. The equal-orientation same-leg block retains the Cauchy subtraction. The crossed block uses the second elliptic point on the other leg and the native minus sign.

**Theorem 1.6 (Regular same-orientation diagonal).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The removable diagonal of the Cauchy-subtracted block is the limiting signed J formula with the actual slit-period correction.

**Theorem 1.7 (Half-coordinate differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.half_coordinate_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.half_coordinate_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the squared native coordinate, the signed source is the coefficient of the pullback of dx/(2y). The right-leg lift reverses the differential.

**Theorem 1.8 (Geometric covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_geometric_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_geometric_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restoring only the same-puncture subtraction gives the elliptic kernel multiplied by the two signed half-coordinate differentials.

**Theorem 1.9 (A to B and D covariance differences).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_A_covariance_discrepancy`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_A_covariance_discrepancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The A source on the native convergence overlap gives the period-product differences from the B and D spatial kernels in the pulled-back differential units.

**Theorem 1.10 (Source at the physical puncture).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_source_at_puncture`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_source_at_puncture` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The signed source at zero divided by the chosen root of the physical scale gives the chart's half-differential at the corresponding puncture.

**Theorem 1.11 (Relative puncture signs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_chosen_source_signs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_chosen_source_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the common physical puncture order, the A to B signs are positive except at S and the A to D signs are negative at Q and R.

**Theorem 1.12 (Native source germ on A and B).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected normalized root agrees with the literal signed source germ wherever the A or B period parameter belongs to the native disk.

**Theorem 1.13 (Source at all three puncture charts).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized square root defines an analytic germ at the origin of each spatial coordinate.

**Theorem 1.14 (Native covariance germ on A and B).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_covariance_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_covariance_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The chart kernels agree with the native J-plus-free and minus-T series on their initial A and B convergence overlaps, including both mode origins.

**Theorem 1.15 (Regular chart covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_covariance_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_covariance_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With the chosen source roots and actual period corrections, every signed covariance is jointly analytic at the pair of mode origins in A, B and D.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_chosen_source_signs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_covariance_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_covariance_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chart_source_at_puncture`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.chosen_chart_source_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.half_coordinate_pullback`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_A_covariance_discrepancy`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_covariance_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_diagonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_geometric_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_mean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_mean_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_spatial_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap.native_tagged_entry`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Applications](../ComplexRadial/Applications.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource](OriginalFourMPeriodSource.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic](../OriginalGaussianSewnAnalytic.md)
