# Local branch and adjacent slit germ

## Abstract

Native signed mean at the D-channel boundary

**Definition 1.1 (D-lip half-current source).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive sign keeps the slit mean. The negative sign uses the principal inverse square root of −h/b with factor b⁻¹ and the lip phase. That phase is −i for the lower D lip and +i for the upper D lip.

**Theorem 1.2 (Holomorphic germ at the D boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_joint_analytic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_joint_analytic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At (0,t) for real t > 1, either lip formula is jointly analytic in the external variable and radial parameter. The reflected branch argument for the negative sign is t−1 at the centre.

**Theorem 1.3 (Agreement on the designated open lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_eventuallyEq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_eventuallyEq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each fixed r on the chosen open D lip, the D-lip mean agrees with the slit mean on a neighborhood of u = 0. The imaginary part of h/b retains its sign near that centre, where the inverse half-power phase identity applies.

**Theorem 1.4 (Nonvanishing of the sum of weighted means).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipWeighted_sum_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipWeighted_sum_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At t > 1 the weighted means are 1 for the positive sign and a nonzero purely imaginary number for the negative sign. Equal signs give twice the same nonzero factor, and mixed signs give real part 1.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_eventuallyEq`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipMean_joint_analytic`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDLipMean.dLipWeighted_sum_ne_zero`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean](OriginalFourMSlitMean.md)
