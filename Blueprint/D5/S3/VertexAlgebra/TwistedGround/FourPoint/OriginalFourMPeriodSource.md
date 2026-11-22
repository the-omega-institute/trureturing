# Euler periods in the physical charts

## Abstract

Periods and covariance of the original four-point kernel

Write P for the original Euler slit period and τ(r) for i P(1−r)/P(r). At the real cross-ratio z the native arguments are rA = 1−1/z, rB = z and rD = 1/z.

**Definition 1.1 (Period correction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.periodCorrection`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.periodCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a complex function F and complex r, the correction C_F(r) is r(1−r) deriv(F)(r)/F(r).

**Theorem 1.2 (Pfaff transport of the correction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.pfaff_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.pfaff_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For r in the Euler slit domain, differentiating the principal Pfaff identity gives C_P(r/(r−1)) = C_P(r)/(1−r) − r/[2(1−r)].

**Theorem 1.3 (Correction at the Pfaff image of A).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real z > 0, the Pfaff image of rA is 1−z. The transported correction is C_P(1−z) = z C_P(rA) + (1−z)/2.

**Definition 1.4 (The D lip paired with A).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dLip`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dLip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the Boolean upperA, the D lip is the open half-plane Im t < 0 when upperA is true and Im t > 0 when upperA is false.

**Theorem 1.5 (The open D lip lies in the double slit).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dLip_mem_doubleSlit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dLip_mem_doubleSlit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both choices of D lip have nonzero imaginary part, so their points lie in the canonical Euler double slit.

**Definition 1.6 (The D period germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Boolean upperA and complex t, set s = 1 when upperA is true and s = −1 when it is false. Then dPeriod(upperA,t) = (τ(1−1/t)+s) P(1−t)/i.

**Theorem 1.7 (Analyticity of the D period at the boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_analyticAt`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_analyticAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either lip and every real t > 1, the continued D period is complex analytic at t.

Compose the analytic Euler period and period ratio with the two boundary coordinates 1−t and 1−1/t. The first is in the Euler slit and the second is in the double slit. Multiply the period by the shifted ratio and divide by i.

**Theorem 1.8 (Nonvanishing of the D period at the boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either lip and every real t > 1, the continued D period is nonzero at t.

The imaginary part of the ratio at 1−1/t is positive, so either real shift preserves nonvanishing. The Euler period at 1−t is nonzero.

**Theorem 1.9 (Agreement with the Euler period on the open lip).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At every complex point of the selected D lip, dPeriod(upperA,t) = P(t). The complementary ratio at 1−t differs from the ratio at its Pfaff image 1−1/t by s.

**Theorem 1.10 (One-sided period and derivative limits).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either choice of upperA and every real t > 1, as u tends to t within the selected D lip, P(u) tends to dPeriod(upperA,t) and deriv(P)(u) tends to the complex derivative of dPeriod(upperA,·) at t.

**Theorem 1.11 (A real germ comparison gives equality near an interior lip point).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.eq_near_dLip_of_real_germ`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.eq_near_dLip_of_real_germ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F and G be complex analytic at a real t. Suppose F and G agree on a real neighborhood of t, and G agrees with D as the complex argument approaches t within the selected lip. The punctured real neighborhood supplies complex accumulation at t. The analytic identity theorem extends equality of F and G to a complex neighborhood of t. The selected open half-plane meets every neighborhood of t, so F and D agree on a full complex neighborhood of some interior point of that lip.

**Definition 1.12 (Corrections in native chart arguments).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartCorrection`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Boolean upperA, a chart c and complex z, chartCorrection applies the period correction at parameter(c,z). It uses P in A and B and dPeriod(upperA,·) in D.

**Theorem 1.13 (Pfaff period with the chosen A root).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_period`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real z > 0, P(1−z) = periodRoot(A,z) P(rA), where periodRoot(A,z) = 1/√z.

**Theorem 1.14 (The two corrected spatial covariance differences).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.covariance_discrepancies`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.covariance_discrepancies` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let upperA select a lip, let z be real with 0 < z < 1, and take complex x and X with zx−1, zX−1 and x−X nonzero. For each chart, subtract its chartCorrection from spatialKernel at first argument 1−r, using the native argument r of that chart. Evaluate the resulting kernels K_A, K_B and K_D at (x,X), at the two pullB images and at the two pullD images, respectively.

Then (−i√z)² K_A − K_B = 1/[π P(1−z) P(z)] and i² K_A − K_D = 1/[π P(rA) dPeriod(upperA,rD)].

**Theorem 1.15 (The principal root on the D boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartD_root_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartD_root_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0 < z < 1, let u tend to rD within the selected D lip. The principal complex power (1−u)^(1/2) tends to i√(1−z)/√z on the lower lip (upperA true) and to −i√(1−z)/√z on the upper lip (upperA false). The lower limit is periodRoot(D,z).

**Theorem 1.16 (The shifted theta exponents).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chart_source_exponents`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chart_source_exponents` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For either lip and real 0 < z < 1, take any lattice data D and complex source vectors M_B and M_D indexed by its rank. Write Q(M) = Mᵀ G M for the Gram quadratic form with the integer matrix G cast to the complex numbers.

Use (p_B,q_B) = (P(1−z),P(z)) and (p_D,q_D) = (P(rA),dPeriod(upperA,rD)). The source lifts are a_B = periodRoot(A,z)(−i√z) and a_D = i. In each chart j = B,D put ζ_j = [i a_j/(2π p_j)] M_j and τ_j = i q_j/p_j. Both identities 2πi Q(ζ_j)/τ_j = Q(M_j)/(2π p_j q_j) hold.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_correction`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartB_pfaff_period`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartCorrection`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chartD_root_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.chart_source_exponents`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.covariance_discrepancies`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dLip`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dLip_mem_doubleSlit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_analyticAt`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_eq_slit`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.dPeriod_ne_zero`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.eq_near_dLip_of_real_germ`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.periodCorrection`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPeriodSource.pfaff_correction`
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialPfaffNome](../../../Analytic/OriginalHalfBinomialPfaffNome.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMActualChart](OriginalFourMActualChart.md)
