# Fixed occupations and finite lowering

## Abstract

Continuation of the native lowered D-lip Laurent channel and A/D overlap

**Definition 1.1 (Fixed-occupation D-lip charge sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either lip, fix a mod-two class and four occupations. Sum over the charges in that class. Each term multiplies the inverses of (1−t)³ and the twelfth power of the continued D period by the D nome raised to the natural part of the charge energy and by the affine Gaussian coefficient for the fixed occupations. The matrix entries are successive Taylor coefficients at the external origins of the Gram-scaled signed covariance. The vector takes the corresponding mean coefficients with minus the leg sign, inverse period, and pairing of the label's unit charge with the summation charge.

**Theorem 1.2 (Analyticity of the D-lip charge sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_analyticAt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_analyticAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real positive definite Gram data, either lip, every mod-two class and all four occupations, the corresponding sector is complex analytic at each real t > 1. Nonvanishing of the boundary period gives the analytic determinant factor. Apply `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.analytic_coefficient_slice` once to the joint mean and twice to the joint covariance. The tagged entries form a finite family, so they are analytic on a common ball where the determinant and nome are analytic and the nome has modulus less than one. On that ball apply `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.charge_sector_differentiableOn` and use complex differentiability on the ball.

**Definition 1.3 (Native lowered D-lip Laurent channel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each mod-two class a, weight the lowered Laurent sum by the quadratic sign of a+b. The detector sums ell below the canonical lowering cutoff, with the canonical lowering weight at m+n+r. It uses input order P, R, Q and applies ell powers of the oscillator lowering operator to S. Each Laurent term has factor (−t) raised to −(H+L) and uses the shared occupation projection at weights H and L, Taylor degree zero, and Laurent index m+n+r+ell−H−L+1. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.loweringCutoff`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.loweringWeight`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.projectOccupations`.

**Theorem 1.4 (Analyticity of the lowered D-lip Laurent channel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_analyticAt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_analyticAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any lattice data with positive definite real Gram matrix, either lip, all nonnegative weights H, K, L, integer modes m, n, r, oscillator inputs P, Q, R, S and mod-two output charge b, the channel is complex analytic at each real t > 1. Unfold the shared occupation projection into its finite weighted sum of analytic sectors. The Laurent power is analytic because t is nonzero. Then take the finite lowering and charge-class sums with their coordinate-independent weights and quadratic signs.

**Theorem 1.5 (Agreement of fixed-occupation sector sums on the open D lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_eq_slit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_eq_slit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either selected lip, each mod-two class and all four fixed occupations, the D-lip coset sum equals the canonical slit coset sum at every point of the open lip. The period and nome agree there. Transport the mean germ through its Taylor coefficient and the covariance germ through both successive coefficients. The resulting matrices, signed linear factors and energy weights agree term by term. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.coefficient_congr`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector`

**Theorem 1.6 (Agreement with the canonical D channel on the open lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_eq_slit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_eq_slit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lattice datum, the native D-lip channel and the canonical slit D channel agree at every point of the selected open lip. Apply sector agreement inside the shared occupation projection and use the same lowered Laurent detector and charge-class signs. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_eq_slit`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelD`

**Theorem 1.7 (Conditional interior A/D chart overlap).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.slit_AD_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.slit_AD_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a positive definite real Gram matrix and a real t greater than one. Explicitly assume that A at 1−s equals the continued D-lip channel at s throughout a real neighborhood of t. Complex analyticity on both sides of the equality gives agreement near t. Open-lip channel agreement gives equality with canonical D near an interior point u of that lip. Inversion gives y = u⁻¹ in U_A ∩ U_D and equality of A(1−z⁻¹) and D(z⁻¹) throughout a complex neighborhood of y. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.eq_near_dLip_of_real_germ`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelA_analyticOnNhd`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_analyticAt`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_eq_slit`

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.loweringCutoff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.loweringWeight`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.projectOccupations`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.slit_AD_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.eq_near_dLip_of_real_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.charge_sector_differentiableOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelA_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelD`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.analytic_coefficient_slice`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.coefficient_congr`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients](FourPointChannelCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance](OriginalFourMDLipCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome](OriginalFourMDLipNome.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms](OriginalFourMSlitChartGerms.md)
