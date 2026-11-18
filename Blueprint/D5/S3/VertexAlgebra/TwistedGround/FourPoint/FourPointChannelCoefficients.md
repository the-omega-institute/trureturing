# Laurent Coefficients of the Actual Four-Point Channels

## Abstract

Laurent Coefficients of the Actual Four-Point Channels.

**Definition 1.1 (Diagonal numerator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.IsDiagonalNumerator`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.IsDiagonalNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The numerator is holomorphic at zero and its coefficient of order E is the original coset kernel at the two signed modes H+K−E−1 and E+(s−H−K+1).

**Definition 1.2 (Canonical actual numerator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the sum of the rescaled Taylor series of the original coset at right mode E+(s−H−K+1) in degree E.

**Theorem 1.3 (Exact coefficients and sewn pullback).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator_spec`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact energy-coefficient formula identifies every Taylor coefficient with the native coset kernel. Uniqueness of the sum on the common disk transfers the negative-square pullback to the canonical numerator. The pullback equals the even part of the actual Laurent-projected sewn charge sum.

**Theorem 1.4 (Iterate residue).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelA`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelA` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Extract the coefficient of the simple pole after multiplying the Laurent germ by the signed power tʳ and the binomial factor (1+t)ᵐ.

**Theorem 1.5 (B-channel residue).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelB`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelB` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the finite lowering sum to the permuted inputs Q, R, P and use the detector lowered ell times at summed mode m+n+r+ell. The weight is tⁿ(1−t)ʳ.

**Theorem 1.6 (D-channel residue).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelD`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelD` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the permuted inputs P, R, Q and the lowered detector at summed mode m+n+r+ell. The weight tᵐ(t−1)ʳ yields the original D sign.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.IsDiagonalNumerator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator_spec`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelA`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelB`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelD`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeGerm](OriginalFourMChargeGerm.md)
