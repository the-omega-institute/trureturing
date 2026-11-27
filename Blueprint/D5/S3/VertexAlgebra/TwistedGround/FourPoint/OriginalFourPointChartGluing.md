# A common function on the twice-punctured plane

## Abstract

Identity-principle gluing on the three four-point chart domains

**Definition 1.1 (Native chart parameter domain).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.Ω`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.Ω` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native argument avoids zero and the real ray from one to infinity. The A, B and D substitutions are 1 − z⁻¹, z and z⁻¹.

**Theorem 1.2 (The A and B domains cover).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_union_U_B`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_union_U_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A excludes the nonpositive real ray and the point one. B excludes zero and the real ray starting at one. Their union is ℂ ∖ {0, 1}.

**Theorem 1.3 (The A and B overlap).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_inter_U_B`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_inter_U_B` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The overlap deletes both real rays, leaving the interval (0, 1) between them. The upper and lower half-planes join through this interval.

**Theorem 1.4 (The inverse chart domain).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_D_eq`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_D_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

D is defined off the closed real segment [0, 1]. It lies in the twice-punctured plane and contains the exterior of the closed unit disk.

**Theorem 1.5 (Gluing A and B by the identity principle).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_gluing`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_gluing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For holomorphic chart functions A and B, assume their equality holds arbitrarily close to a point of the overlap on its punctured neighborhood. The identity principle extends the equality on the preconnected double slit. The local functions thus give one holomorphic function whose restrictions agree with A and B. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_inter_U_B`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_union_U_B`

**Theorem 1.6 (Extending a D comparison from either chart).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.eqOn_D_of_chart_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.eqOn_D_of_chart_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F be holomorphic on ℂ ∖ {0, 1} and let D be holomorphic on U_D. Assume F agrees with C on an open set U and C = D accumulates at a point of U ∩ U_D. The identity principle extends F = D throughout the preconnected domain U_D. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_D_eq`

**Theorem 1.7 (Restrictions give the three punctured germs).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.germs_of_eqOn`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.germs_of_eqOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Near one the A domain supplies the restriction, near zero the B domain supplies it, and near zero in the inverse coordinate the D domain supplies it.

**Theorem 1.8 (Gluing native channel functions with the B prefactor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_common_four_point_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_common_four_point_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A, B and D be holomorphic on Ω. For integer k, suppose A(1 − z⁻¹) = 2¹² zᵏ B(z) accumulates at a point of the double slit. Suppose A(1 − z⁻¹) = D(z⁻¹) accumulates at a point of U_A ∩ U_D, or 2¹² zᵏ B(z) = D(z⁻¹) accumulates at a point of U_B ∩ U_D. On the punctured neighborhood of native zero, assume A(t) agrees with raw A at −t, and B(t) and D(t) agree with raw B and raw D at t. There is then a common function holomorphic on ℂ ∖ {0, 1}. At one its punctured germ is raw A at (1 − z)/z. At zero its germ is 2¹² zᵏ times raw B at z. In the inverse coordinate z = u⁻¹ its germ at u = 0 is raw D at u. `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_gluing`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.eqOn_D_of_chart_overlap`, `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.germs_of_eqOn`

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_inter_U_B`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_inter_U_B`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_union_U_B`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_A_union_U_B`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_D_eq`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.U_D_eq`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.eqOn_D_of_chart_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.eqOn_D_of_chart_overlap`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_common_four_point_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_gluing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.exists_gluing`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.germs_of_eqOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.germs_of_eqOn`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing.Ω`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialSlitPeriod](../../../Analytic/OriginalHalfBinomialSlitPeriod.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMActualChart](OriginalFourMActualChart.md)
