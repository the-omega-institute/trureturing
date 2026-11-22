# Joint reflection at the D boundary

## Abstract

Schwarz reflection of the native signed D-lip germs

**Theorem 1.1 (Reflection of the signed mean).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection.dLipMean_upper_reflection`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection.dLipMean_upper_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either external sign and real t > 1, the upper mean near (0,t) equals the conjugate of the lower mean at the conjugate pair. The inverse square root stays on its principal branch and conjugation exchanges the two explicit lip phases.

**Theorem 1.2 (Reflection of the full covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection.dLipCovariance_upper_reflection_joint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection.dLipCovariance_upper_reflection_joint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each real t > 1 and all leg and sign choices, the upper covariance near (0,0,t) equals the conjugate of the lower covariance evaluated at the conjugates of both local coordinates and of the D parameter. Differentiate the Euler D-period reflection to transport r(1−r)P′(r)/P(r). Apply the mean reflections to the weighted denominator and keep the Cauchy term for opposite external signs on the same leg. The mixed-leg rational kernel is conjugated in its own branch.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection.dLipCovariance_upper_reflection_joint`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipReflection.dLipMean_upper_reflection`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipCovariance](OriginalFourMDLipCovariance.md)
