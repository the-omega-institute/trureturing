# Common native coordinates and the B and D comparisons

## Abstract

Finite Gaussian and charge-sector products on the original four-point charts

Write P = slitPeriod, p_A = P(1−1/x), p_Pf = P(1−x), p_B = P(x), p_D = dPeriod(upperA,1/x), t_B = i p_B/p_Pf and t_D = i p_D/p_A. On the real overlap 0 < x < 1, p_Pf = R_A p_A for R_A = periodRoot(A,x) = (√x)⁻¹. The D period takes the lower lip for upperA = true, with t_D = t_B + 1, and the upper lip for upperA = false, with t_D = t_B − 1. Use the lift factors b_B = −i√x and b_D = i.

**Definition 1.1 (External sample in native A coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.Sample`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.Sample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A sample for D records the Boolean right-leg and outgoing-mode flags, a complex half-coordinate q and a colour in Fin(rank D). In a family indexed by a finite type, multiple samples may use the same puncture and colour.

**Definition 1.2 (Period-normalized Gaussian times the sector theta function).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.chartProduct`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.chartProduct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take lattice data D with unit integral Gram determinant, a finite family of samples with complex weights ωⱼ, either upperA, real x, complex w, a chart c and a mod-two charge a. Write mⱼ for signedHalfSource at the flags of sample j and arguments (qⱼ²,w²). The respective A, B and D differentials m_{c,j} are mⱼ, mⱼ/b_B and mⱼ/b_D.

Let K(j,k) be covarianceMode at the leg and outgoing flags of j,k and arguments (qⱼ²,qₖ²,w²). Use K_c(j,k) = K(j,k) − Δ_c m_{c,j}m_{c,k}. In chart order A, B, D the corrections Δ_c are 0, 1/(π p_Pf p_B) and 1/(π p_A p_D), and the theta periods τ_c are t_D, −1/t_B and −1/t_D. All three covariances use the native A free subtraction.

With G the original Gram matrix cast to ℂ and colour uⱼ at sample j, put E_c = (∑ⱼ ∑ₖ ωⱼωₖ G[uⱼ,uₖ] K_c(j,k))/2 and M_c(u) = ∑_{j : uⱼ = u} ωⱼ m_{c,j}. The product at a is (p_c¹²)⁻¹ exp(E_c) chargeTheta(a,τ_c,i M_c/(2πp_c)).

**Theorem 1.3 (A-to-D and A-to-B with the exact finite charge factors).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_chart_product`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_chart_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume G has unit determinant over ℤ, is positive definite over ℝ and rank D is 24. Take real 0 < x < 1, either upperA, arbitrary complex w, any finite sample family with complex weights and any mod-two charge a. Write A(a), B(a), D(a) for the respective products at that charge.

Then D(a) = 2⁻¹² ∑_b F(a,b) A(b) and B(a) = (R_A¹²)⁻¹ (2⁻¹² ∑_b F(a,b) ε(b) A(b)), with F = fourierSign, ε = quadraticSign and b ranging over all mod-two charges. The S multipliers cancel the Gaussian covariance corrections. The B source picks up a minus sign under S, which disappears by q ↦ −q within each charge fiber. The period translation by either lip contributes ε(b).

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.Sample`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.chartProduct`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMChartProduct.native_chart_product`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMShiftedTheta](OriginalFourMShiftedTheta.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSignedCovariance](OriginalFourMSignedCovariance.md)
