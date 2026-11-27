# Same-leg and opposite-leg kernels

## Abstract

Native signed covariance on the Euler slit

**Definition 1.1 (Regularized same-leg kernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitJ`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitJ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the two slit means by r/4 minus the slit period correction plus the regularized rational term. Its denominator contains the square of the sum of the two means weighted by their respective h factors.

**Definition 1.2 (Opposite-leg kernel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitT`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitT` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the two slit means by the signed opposite-leg rational kernel minus the slit period correction.

**Definition 1.3 (Signed slit covariance generator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For equal legs use the same-leg kernel with the free Cauchy term included for unequal external signs. For distinct legs use the negative of the opposite-leg kernel.

**Theorem 1.4 (Agreement with the native covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_eq_native`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_eq_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of legs and signs, if ‖u‖ + ‖r‖ < 1 and ‖v‖ + ‖r‖ < 1, the slit covariance equals the native signed covariance generator.

**Theorem 1.5 (Joint holomorphic covariance germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_joint_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_joint_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every point r of the Euler slit, the covariance is jointly analytic at (0,0,r) in both external variables and the radial parameter.

At the Taylor centre the two weighted means have positive real parts. Their sum and the opposite-leg rational denominator are nonzero there, and the mixed-sign free term is analytic there.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitCovariance_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitJ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance.slitT`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean](OriginalFourMSlitMean.md)
