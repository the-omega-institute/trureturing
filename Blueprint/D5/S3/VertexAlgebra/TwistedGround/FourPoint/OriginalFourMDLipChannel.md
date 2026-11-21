# Fixed occupations and finite lowering

## Abstract

Analyticity of the native lowered D-lip Laurent channel

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

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.loweringCutoff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.loweringWeight`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.projectOccupations`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChannel_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipChannel.dLipChargeSector_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.charge_sector_differentiableOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor.analytic_coefficient_slice`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients](FourPointChannelCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance](OriginalFourMDLipCovariance.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipNome](OriginalFourMDLipNome.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation](OriginalFourMSectorContinuation.md)
