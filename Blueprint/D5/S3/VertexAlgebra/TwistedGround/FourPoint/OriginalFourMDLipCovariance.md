# Boundary germ and slit agreement

## Abstract

Native signed covariance at the D-channel boundary

**Definition 1.1 (D-lip covariance generator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the two D-lip means and the correction of the D period in the signed covariance. The equal-leg branch uses the weighted means in the regularized denominator and keeps the mixed-sign free term. The unequal-leg branch uses the negative of the corrected opposite-leg kernel times the two means.

**Theorem 1.2 (Covariance agreement on the open lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_eq_of_means`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_eq_of_means` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a parameter on the designated open D lip, equality of the D-lip and slit means at both external arguments gives equality of the covariances. The period correction agrees there because the two periods and their derivatives agree.

**Theorem 1.3 (Joint holomorphic covariance germ at the D boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_joint_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_joint_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real t > 1, all choices of lip, legs and external signs give an analytic covariance at (0,0,t) in both external variables and the radial parameter. The D period and the weighted same-leg denominator are nonzero at the centre.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_eq_of_means`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance.dLipCovariance_joint_analytic`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean](OriginalFourMDLipMean.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitCovariance](OriginalFourMSlitCovariance.md)
