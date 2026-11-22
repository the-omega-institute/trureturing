# Native cusp germs on the Euler slit

## Abstract

Explicit slit chart germs for the actual rank-24 four-point channels

**Definition 1.1 (The slit diagonal numerator).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitDiagonal`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Project the canonical slit sector values onto fixed occupations at weights H and K, Taylor degree zero and Laurent index s−H−K+1. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.projectOccupations`

**Definition 1.2 (The lowered slit Laurent projection).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitLowered`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitLowered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the shared finite lowering and Laurent detector to the slit diagonal numerators with the original Laurent sign. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.loweredLaurent`

**Definition 1.3 (The continued A channel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelA`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Project the slit charge-sector sums onto the diagonal with offset s − H − K + 1 at energy zero. Multiply each diagonal by (−t)^(−H−K) and sum the classes with the quadratic and Fourier signs. This is A as a function of its native parameter t. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector`

**Definition 1.4 (The continued B channel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelB`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

In class b, sum the slit Laurent diagonals for Q, R, P over the native finite lowering cutoff. The term of order ℓ uses the detector lowered ℓ times, diagonal sum m + n + r + ℓ and the original lowering weight.

**Definition 1.5 (The continued D channel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelD`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the corresponding lowering sum for P, R, Q in the inverse parameter. The sector of class a has the quadratic sign of a + b.

**Theorem 1.6 (Holomorphy of the canonical A channel).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelA_analyticOnNhd`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelA_analyticOnNhd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive definite real Gram data the A channel is complex analytic at every point of the punctured Euler slit. The finite occupation projection and charge-class sum preserve the holomorphy of the slit sectors, and the Laurent power has no pole on this domain. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector_differentiableOn`

**Theorem 1.7 (Holomorphy and the actual cusp germs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChartGerms`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChartGerms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a positive definite real Gram matrix, rank 24 and unit Gram determinant. Finite occupation projection preserves holomorphy of the continued charge-sector sums. On the opening disk the actual sewn diagonal at w and at −w equals the same slit diagonal at w². Their average is the actual numerator at −w² near zero. Substituting the complex square root of t, which tends to zero with t and squares to t, identifies the slit diagonal at t with the actual numerator at −t. The Laurent factor and the finite charge and lowering sums give holomorphy on the punctured slit and the punctured germs at t = 0. The A germ is actual A at −t, and the B and D germs are actual B and D at t. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector_differentiableOn`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeTerm_eq_native`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator_spec`

**Theorem 1.8 (The mode identity conditional on the two slit crossing equalities).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.identityK_of_slitChart_crossing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.identityK_of_slitChart_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume rank 24 and a positive definite real Gram matrix with unit determinant. For every output class, suppose A(1 − z⁻¹) = 2¹² z^(m+n+r+2) B(z) accumulates at an interior point of the double slit. Suppose either A(1 − z⁻¹) = D(z⁻¹) accumulates at a point of U_A ∩ U_D, or 2¹² z^(m+n+r+2) B(z) = D(z⁻¹) accumulates at a point of U_B ∩ U_D. The explicit slit functions give holomorphy and punctured germs at native zero, with actual A at −t and actual B and D at t. The gluing and residue argument gives the original identity K for the signed modes. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChartGerms`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_native_chart_germs`

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.actualDiagonalNumerator_spec`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients.loweredLaurent`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChargeNormal.projectOccupations`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeSector_differentiableOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation.slitChargeTerm_eq_native`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.identityK_of_slitChart_crossing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelA`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelA_analyticOnNhd`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelB`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChannelD`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChartGerms`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitChartGerms`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitDiagonal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitChartGerms.slitLowered`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK.identityK_of_native_chart_germs`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSectorContinuation](OriginalFourMSectorContinuation.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointIdentityK](OriginalFourPointIdentityK.md)
