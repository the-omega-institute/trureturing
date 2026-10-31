# A Linear Excursion of the Actual Arithmetic Kernel

## Abstract

Failure of RH forces a linear excursion of the complete actual arithmetic kernel.

**Theorem 1.1 (The literal arithmetic kernel exceeds its linear envelope).**

$$\neg \operatorname{RiemannHypothesis} \Rightarrow \left(\exists y \in \mathbb{R},\; \operatorname{log}\left(10000\right) \le y \land 4 \cdot y + 9 < \operatorname{exp}\left(\frac{-y}{2}\right) \cdot \left(\operatorname{U}\left(\operatorname{exp}\left(y\right)\right) - \operatorname{log}\left(2 \cdot \pi\right) + \operatorname{trivialT}\left(y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_linear_peak_of_not_rh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is CompleteMertensPeak.U, containing all prime-power endpoints, and trivialT is the complete trivial-zero correction. The conclusion has no zero-simplicity, prime-number-theorem or additional transform hypothesis. It provides no quantitative upper bound for the first excursion.

Set T=log(10000) and k(t)=exp(-t/2)*Re(actualH(t)). The actual complete zero package supplies continuity and reality. Denying the excursion makes 4t+9-k(t) nonnegative on t>T. Use this as an ENNReal density against restricted volume; the resulting measure may have infinite total mass. The actual exponential bound proves its negative moments with parameter less than -1/2.

For P(z)=complexMGF(id,mu)(-z), the actual Laplace identity gives P=A-N/(z^2-1/4) initially in Re(z)>1/2. Here N=M*z-X'/X, X(z)=xiReading(z+1/2), M=firstLiMass and A=B+C. The polynomial tail B=exp(-z*T)*((4T+9)/z+4/z^2) is obtained by differentiating the restricted-volume transform. The compact correction C is entire by dominated parameter differentiation without differentiating k.

Continue the cross identity (z^2-1/4)*X*P=((z^2-1/4)*A-M*z)*X+X' on the actual open convex convergence domain. Every positive real belongs to the zero-free domain of X, by the original actual height theorem. Endpoint normalization gives N(1/2)=0, so the holomorphic quotient is dslope(N,1/2,z)/(z+1/2). Analytic punctured uniqueness supplies neighborhood equality also at 1/2.

NonnegativeBoundary.integrable_exp_on_real_ray applies at every real interior convergence point and forces all negative moments. The same cross identity now yields X'=G*X throughout Re(z)>0. The existing analytic_linear_ode_zero_free compares finite positive analytic orders at a hypothetical zero, handling all multiplicities. The right-half-strip reduction proves RH under denial. Finally the actual integrated explicit formula, used only at y>=T>0, restores the literal arithmetic conclusion.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak.actual_linear_peak_of_not_rh`
- Dependency: [D5/S3/Analytic/Laplace/NonnegativeBoundary](../../../Analytic/Laplace/NonnegativeBoundary.md)
- Dependency: [D5/S3/Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup](../../../Analytic/ShiftedXiPoisson/ShiftedPoissonSemigroup.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/WholeFormula](WholeFormula.md)
- Dependency: [D5/S3/Weil/Probability/AnalyticLogarithmicContinuation](../../Probability/AnalyticLogarithmicContinuation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/RightHalfStripRiemannReduction](../../ZetaBridge/RightHalfStripRiemannReduction.md)
