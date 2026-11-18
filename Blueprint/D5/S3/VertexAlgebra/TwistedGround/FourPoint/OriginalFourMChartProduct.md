# Four-Point Gaussian and Theta Product

## Abstract

Rank-24 cancellation for the native four-point Gaussian and charge-sector product

**Theorem 1.1 (Pulled covariance in common coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.pulled_covariance_off_diagonal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.pulled_covariance_off_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Off the geometric poles the signed A overlap gives the B and D elliptic covariances with the common A free subtraction. The original mixed free block is included.

**Theorem 1.2 (Native signed charge mean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_sample_mean`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_sample_mean` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual Gaussian mean sums to the signed half-coordinate source contracted with the colour and charge and divided by the slit period.

**Theorem 1.3 (Physical source signs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.physical_source_signs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.physical_source_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The relative sign at S in the B chart and at Q and R in the D chart agrees with the chosen lift at each physical puncture.

**Theorem 1.4 (Original charge fiber).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.chart_product_charge_sum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.chart_product_charge_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product is the original mod-two charge sum. Its linear exponent is the weighted sum of the signed transported charge means.

**Theorem 1.5 (Native rank-24 determinant).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_rank24_determinant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_rank24_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the open disk the oscillator determinant contributes the inverse third power of one minus the period argument and the inverse twelfth power of the Euler period.

**Theorem 1.6 (Complementary cancellation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_chart_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_chart_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite family of external source weights the forward theta exponential cancels the Gram-contracted Gaussian correction. The D comparison uses the normalized original Fourier row. The B comparison first uses the Pfaff translation and then complementary inversion, with the quadratic sign in the Fourier summand and the inverse twelfth power of the Pfaff root.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.chart_product_charge_sum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_chart_product`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_rank24_determinant`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_sample_mean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.physical_source_signs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.pulled_covariance_off_diagonal`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta](OriginalFourMShiftedTheta.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedOverlap](OriginalFourMSignedOverlap.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianPeriodIdentity](../OriginalGaussianPeriodIdentity.md)
