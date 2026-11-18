# Physical Four-Point Covariance Transport

## Abstract

Covariance and marked Gaussian coefficients in the four-point charts

**Theorem 1.1 (Covariance in the physical coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.signed_physical_covariance_transport`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.signed_physical_covariance_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The elliptic kernel transports between all three charts after removing the native same-puncture Cauchy correction and retaining the mixed free block. The identity extends across coincident positions by regularity of the two kernels.

**Theorem 1.2 (Marked Gaussian coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.marked_gaussian_jet`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.marked_gaussian_jet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation in an independent variable for each marked oscillator gives the native affine coefficient times the product of the occupation factorials. The oscillator label map can have repeated colours and modes.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.marked_gaussian_jet`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalCovariance.signed_physical_covariance_transport`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport](OriginalFourMOccupationTransport.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFixedExternalCoefficient](../OriginalGaussianFixedExternalCoefficient.md)
