# The Original Four-Point Identity from the Actual Channel Germs

## Abstract

The Original Four-Point Identity from the Actual Channel Germs.

**Definition 1.1 (Actual A germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelA`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The iterate Laurent series in (1−z)/z is summed over charge sectors with the original quadratic and Fourier signs.

**Definition 1.2 (Actual B germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelB`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the original lowered row at weights K and L with the inputs Q, R, P. The common scalar inserts the prefactor 2¹²z^(m+n+r+2).

**Definition 1.3 (Actual D germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelD`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the lowered row at weights H and L with the inputs P, R, Q in the inverse coordinate. Sum it with the original shifted quadratic signs.

**Theorem 1.4 (The residue identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_four_point_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_four_point_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each output sector take the residues of the weighted common germ. At zero it gives 2¹² times channel B. At one it gives the negative of the signed A sum. At infinity it gives the negative of the signed D sum.

**Theorem 1.5 (The original signed-mode identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_actual_channel_germs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_actual_channel_germs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary integer modes, the exact sewn numerator supplies each coefficient premise, including all lowered B and D rows. A common holomorphic function with the three specified actual germs gives the original charge-coset law.

**Theorem 1.6 (The identity from native chart overlaps).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_native_chart_germs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_native_chart_germs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Holomorphic native continuations with the three specified local germs, an A/B interior equality accumulation and a D interior equality accumulation supply the common function. Identifying the physical chart products with these local germs and proving the occupied-channel overlap equalities remains open.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelA`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelB`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelD`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_actual_channel_germs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_four_point_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_native_chart_germs`
- Dependency: [D5/S3/AnalyticClosure/ThreePunctureResidue](../../../AnalyticClosure/ThreePunctureResidue.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients](FourPointChannelCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing](OriginalFourPointChartGluing.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalFourMActualChart](../OriginalFourMActualChart.md)
