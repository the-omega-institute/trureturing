# Local strict positivity of the actual prime kernel

## Abstract

A common short window gives strict positivity for every finite configuration of the complete arithmetic kernel.

**Definition 1.1 (The complete arithmetic kernel).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.K`

*Formalization.* `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.K` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real t, K(t)=exp(-abs(t)/2) times the quantity (U(exp(abs(t)))-log(2*pi)+trivialT(abs(t))). Here U is CompleteMertensPeak.U, with its complete inclusive Mangoldt ramps, and trivialT is the full trivial-zero series with coefficients 1/(2*(n+1)*(2*(n+1)+1)). The value K(0) is the strictly positive first Li mass. The definition is even.

**Theorem 1.2 (One window for all finite complex quadratic forms).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.exists_window_posDef`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.exists_window_posDef` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There exists one real delta with 0<delta<log(2), such that for every natural n at least one and every injective real node map x:Fin(n)->Real satisfying abs(x(i)-x(j))<=delta for every pair, the complex matrix with entries K(x(i)-x(j)) is strictly positive definite. Equivalently, its Hermitian quadratic form is strictly positive for every nonzero family of complex coefficients. The window is chosen before n and x. The diameter inequality is closed, includes n=1, and imposes no lower bound on node separation.

On the positive prime-free window the complete arithmetic formula has derivatives D1=K/2-exp(t/2)+exp(-t/2)*(log(2*pi)+log(1-exp(-2*t))/2) and D2=K/4-exp(t/2)+exp(-t/2)/(exp(2*t)-1). The exponential moment derivative and the ordinary logarithmic power series give these identities without truncating either arithmetic correction. Continuity at zero, D1 tending to negative infinity, t*D1 tending to zero and t*D2 tending to one half select a common interval with K>0, D1<0 and D2>0.

Put r=-D1(delta) and L=delta+K(delta)/r. Both r>0 and L>delta hold. For every abs(t)<=delta, K(t) is the integral over 0<s<=delta of max(s-abs(t),0)*D2(s), plus r*max(L-abs(t),0). Only the weighted density s*D2(s) is asserted integrable. The zero endpoint follows from the primitive s*D1(s)-K(s) and its actual limit, rather than integrability of D2 itself.

The arithmetic inputs are U_eq_complete_ramps, U_exp_continuous, trivialCoeff_hasSum, trivialT_continuousOn, firstLiMass_split and first_li_coefficient_pos. Differentiation reuses the original ExpRatioCM.Series weightedSeries, summable_weighted and hasDerivAt_weighted, the pinned Mathlib logarithmic power series, and log_one_sub_exp_derivatives. The endpoint integral reuses Mathlib intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto; positive mixtures reuse PositiveDefinite.Closure.integral. These general suppliers do not identify the actual positive representer on their own.

A triangle is the overlap integral of translated interval indicators. Thus its complex quadratic form is an integral of a squared modulus. For a nonzero coefficient family the leftmost node carrying a nonzero coefficient has a positive interval on which only that coefficient contributes. The wide atom supplies strict positivity; the positive density supplies a positive semidefinite remainder.

This is an unconditional local arithmetic statement. Global positivity, the Riemann hypothesis and the complete signed Robin residual are not conclusions of this theorem.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.K`
- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelLocalPositivity.exists_window_posDef`
- Dependency: [D5/S3/Analytic/ExpRatioCM/Series](../../../Analytic/ExpRatioCM/Series.md)
- Dependency: [D5/S3/Analytic/Fourier/PositiveDefinite/Closure](../../../Analytic/Fourier/PositiveDefinite/Closure.md)
- Dependency: [D5/S3/Analytic/Interpolation/LogOneSubExpDerivatives](../../../Analytic/Interpolation/LogOneSubExpDerivatives.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtLaplace](CompleteMangoldtLaplace.md)
