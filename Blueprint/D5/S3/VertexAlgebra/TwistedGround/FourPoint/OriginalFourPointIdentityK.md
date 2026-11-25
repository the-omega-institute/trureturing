# The residue proof of the charge-coset identity

## Abstract

The original signed-mode identity from common four-point germs

**Definition 1.1 (Actual A germ in the residue coordinate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelA`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the Laurent diagonals of the actual sewn numerators. Sum over input charge classes a with the quadratic sign of a and the Fourier sign for a and the output class b.

**Definition 1.2 (Actual B germ before the prefactor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelB`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In the output class b, use the reflected Laurent diagonal on Q, R, P and the finitely lowered detector S, with the original lowering weights. The chart multiplies this germ by 2¹² z^(m+n+r+2).

**Definition 1.3 (Actual D germ in the inverse coordinate).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelD`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the reflected Laurent diagonals on P, R, Q and the finitely lowered detector S. Sum over classes a with the quadratic sign of a + b.

**Theorem 1.4 (The signed-mode identity from three Laurent expansions).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_four_point_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_four_point_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Gram matrix is positive definite with unit determinant and the three analytic numerator families have the Taylor coefficients of the original diagonal coset kernels. For each output class b, let F be holomorphic on ℂ ∖ {0, 1}. Assume its punctured germs are the A combination at (1 − z)/z near one, 2¹² z^(m+n+r+2) times the B combination at z near zero, and the D combination at u near u = 0 in the coordinate z = u⁻¹. Apply residue balance to (1 − z)^r z^(−m−r−2) F(z) dz. At zero the B prefactor leaves 2¹² z^n (1 − z)^r times the B germ. At one the iterate Jacobian produces the negative signed A residue in the variable t = (1 − z)/z. Inversion gives the negative signed D residue, with weight u^m (u − 1)^r. The sum of these three simple coefficients is exactly the original charge-coset identity for the signed modes m, n, r. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelA`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelB`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelD`, `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart_residue_invariant`, `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_differential_expansions`

**Theorem 1.5 (Specializing to the actual sewn numerators).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_actual_channel_germs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_actual_channel_germs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With a positive definite Gram matrix of unit determinant, the sewn diagonal specification supplies the numerator hypotheses for all three channels, including every term below the B and D lowering cutoff. For each output class, assume a common function holomorphic on ℂ ∖ {0, 1} with punctured germs given by actual A at (1 − z)/z near one, 2¹² z^(m+n+r+2) times actual B at z near zero, and actual D at u near u = 0 for z = u⁻¹. These hypotheses give the original identity. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator_spec`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_four_point_germ`

**Theorem 1.6 (From native chart germs and overlap equalities to the identity).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_native_chart_germs`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_native_chart_germs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Gram matrix is positive definite with unit determinant. For each output class, take A, B and D holomorphic on the punctured Euler slit. At native zero their punctured germs agree with actual A at −t and actual B and D at t, respectively. Assume A(1 − z⁻¹) = 2¹² z^(m+n+r+2) B(z) accumulates at an interior point of the double slit. Assume either A(1 − z⁻¹) = D(z⁻¹) accumulates at a point of U_A ∩ U_D, or 2¹² z^(m+n+r+2) B(z) = D(z⁻¹) accumulates at a point of U_B ∩ U_D. Gluing supplies the common function used in the residue proof. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_common_four_point_germ`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_actual_channel_germs`

## References

- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.aChart_residue_invariant`
- Truth anchor: `D5/S3/AnalyticClosure/ThreePunctureResidue.residue_sum_of_differential_expansions`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator_spec`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelA`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelB`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.hasPrincipalPart_channelD`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_common_four_point_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelA`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelB`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.actualChannelD`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_actual_channel_germs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_actual_channel_germs`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_four_point_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_common_four_point_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_native_chart_germs`
- Dependency: [D5/S3/AnalyticClosure/ThreePunctureResidue](../../../AnalyticClosure/ThreePunctureResidue.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients](FourPointChannelCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMActualChart](OriginalFourMActualChart.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing](OriginalFourPointChartGluing.md)
