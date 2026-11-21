# The critical coefficient for the complete Mangoldt remainder

## Abstract

The additive gap below the critical Mertens envelope

**Theorem 1.1 (The Riemann hypothesis and divergence of the additive gap).**

$$\operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall D \in \mathbb{R},\; \exists T \in \mathbb{R},\; \forall x \in \mathbb{R},\; T \le x \Rightarrow D \le firstLiMass \cdot \sqrt{x} - \operatorname{U}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap.rh_iff_critical_gap_tendsto_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is CompleteMertensPeak.U, the original complete integrated Mangoldt remainder. The coefficient M is firstLiMass. Both the lower bound D and the arguments x range over the reals. The displayed quantifiers unfold convergence to positive infinity.

With y = log x, RH gives a real normalized zero sum F(y) with cosine terms, nonnegative coefficients, and total coefficient mass M. Write d(y) = M − F(y). The product (1 − cos(γy))(1 + cos(γh)) is nonnegative for each zero ordinate γ. Summing this inequality gives 2d(h) − 4d(y) ≤ 2F(y) − F(y+h) − F(y−h).

At positive arguments the explicit formula identifies F with the full arithmetic kernel K, whose value at zero is M. Its derivative tends to negative infinity from the right. The mean value theorem on [0,h] therefore shows that d(h)/h tends to positive infinity as h decreases to zero.

The nonnegative Mangoldt ramps give a weighted midpoint inequality for the normalized arithmetic remainder. At h = exp(−y/2) its smooth part and the correction from the explicit formula give an upper bound proportional to h for the second difference of F. The cosine inequality forces d(y)/h to tend to positive infinity. The bounded additive correction from the explicit formula then gives the stated limit in x. The source derivation is at https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7060395310.

Conversely, divergence of the gap gives U(x) ≤ M√x on a real tail. Substituting x = exp(y) and multiplying by exp(−y/2) bounds G(y) by M. The explicit-formula correction then supplies a constant upper bound for K on a positive tail. The affine-tail criterion for K, used with slope zero, gives RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap.rh_iff_critical_gap_tendsto_atTop`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualLinearPeak](ActualLinearPeak.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/RHSharpActualEnvelope](RHSharpActualEnvelope.md)
