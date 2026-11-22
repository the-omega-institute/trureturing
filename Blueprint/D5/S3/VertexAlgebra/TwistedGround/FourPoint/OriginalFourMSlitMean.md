# Principal branch and Taylor centre

## Abstract

Native signed mean on the Euler slit

**Definition 1.1 (Principal half-current source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Write b(u) = 1−u. For the negative sign use h(e,u,r) = 1−r−u, and for the positive sign use h(e,u,r) = 1−(1−r)u. The source is b(u)⁻¹ times the principal inverse square root of h(e,u,r)/b(u).

**Theorem 1.2 (Agreement with the literal source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_eq_sourceMode`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_eq_sourceMode` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either sign and ‖u‖ + ‖r‖ < 1, the principal expression equals the signed source-mode generator.

**Theorem 1.3 (Joint holomorphic germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_joint_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_joint_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If 1−r lies in the principal slit plane, the source is jointly analytic at (0,r) in the external variable and radial parameter. At u = 0 the branch argument is 1−r for the negative sign and 1 for the positive sign.

**Theorem 1.4 (Positive real part of the regularizing factor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_weighted_re_pos`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_weighted_re_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the Euler slit, h times the source at u = 0 has positive real part. The negative sign gives the principal square root of 1−r and the positive sign gives 1.

**Theorem 1.5 (Analytic period correction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitPeriodCorrection_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitPeriodCorrection_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the Euler period P, the correction r(1−r)P′(r)/P(r) is analytic in a neighborhood of every point of the Euler slit, where P is nonzero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_eq_sourceMode`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitMean_weighted_re_pos`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.slitPeriodCorrection_analyticOnNhd`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance](OriginalFourMSignedCovariance.md)
