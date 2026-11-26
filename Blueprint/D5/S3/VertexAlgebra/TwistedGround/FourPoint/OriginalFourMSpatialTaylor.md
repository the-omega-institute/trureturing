# Ordered coefficients and normal summation

## Abstract

Taylor coefficients on a common polydisk

**Definition 1.1 (Ordered spatial coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor.spatialCoefficient`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor.spatialCoefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take a coordinate list and a nonnegative degree for every coordinate. At each step, replace the selected coordinate by t, take its ordinary Taylor coefficient at t = 0 and leave the other coordinates as parameters. The empty list gives evaluation.

**Theorem 1.2 (Taylor extraction commutes with normal summation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor.spatialCoefficient_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor.spatialCoefficient_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the summands are analytic on one open polydisk about zero and their norms there are bounded by a summable family independent of the point. The sum of their ordered spatial coefficients at zero is the corresponding coefficient of the series. Each coordinate step uses local uniform convergence of complex derivatives and a Cauchy bound on the circle of half the radius. For degree n the new majorant is the old one divided by that radius to power n.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor.spatialCoefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialTaylor.spatialCoefficient_hasSum`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient](../NativeAffineExternalCoefficient.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSewnAnalytic](../OriginalGaussianSewnAnalytic.md)
