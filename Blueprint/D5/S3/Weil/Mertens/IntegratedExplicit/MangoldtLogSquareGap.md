# The real-axis gap at the critical coefficient

## Abstract

Logarithm-squared savings for the integrated Mangoldt remainder

**Theorem 1.1 (A squared-logarithm criterion for the Riemann hypothesis).**

$$\operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall c \in \mathbb{R},\; c < \frac{1}{64} \Rightarrow \left(\exists T \in \mathbb{R},\; \forall x \in \mathbb{R},\; T \le x \Rightarrow \operatorname{U}\left(x\right) \le firstLiMass \cdot \sqrt{x} - c \cdot \operatorname{log}\left(x\right)^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtLogSquareGap.rh_iff_eventually_log_squared_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is CompleteMertensPeak.U and M is firstLiMass. The threshold may depend on the real coefficient c. The inequality holds at every real x above that threshold.

Write y = log x, q = exp(−y/2), h = yq/4 and d(t) = M − K(t). ActualKernelCusp.cusp_quadratic_limit gives d(t)/(t log(1/t)) → 1/2 as t decreases to zero. Since log(1/h)/y → 1/2, the quotient d(h)/(qy²) tends to 1/16.

Under RH the positive cosine weights give the lower bound 2d(h) − 4d(y) for the second difference of K. The midpoint inequality for the Mangoldt ramps bounds that difference from above. After division by qy² its exponential term tends to 1/16, while the residual terms tend to zero. Thus every c below (2/16 − 1/16)/4 gives the asserted eventual saving. The endpoint is not asserted.

Conversely, c = 1/128 gives a gap tending to positive infinity. MangoldtCriticalGap.rh_iff_critical_gap_tendsto_atTop then gives RH. The source derivation is at https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7069599052.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtLogSquareGap.rh_iff_eventually_log_squared_gap`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelCusp](ActualKernelCusp.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap](MangoldtCriticalGap.md)
