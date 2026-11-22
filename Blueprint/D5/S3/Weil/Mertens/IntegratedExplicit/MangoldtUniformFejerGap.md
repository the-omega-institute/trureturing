# The limiting coefficient on a common real tail

## Abstract

A uniform Fejér bound for the complete integrated Mangoldt remainder

**Theorem 1.1 (The squared logarithm and the logarithmic correction).**

$$\operatorname{RiemannHypothesis} \Leftrightarrow \left(\exists C \in \mathbb{R},\; 0 \le C \land \left(\exists T \in \mathbb{R},\; \forall x \in \mathbb{R},\; T \le x \Rightarrow \operatorname{U}\left(x\right) \le firstLiMass \cdot \sqrt{x} - \frac{\operatorname{log}\left(x\right)^{2}}{48} + \frac{\operatorname{log}\left(x\right) \cdot \operatorname{log}\left(\operatorname{log}\left(x\right)\right)}{12} + C \cdot \operatorname{log}\left(x\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtUniformFejerGap.rh_iff_eventually_uniform_fejer_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is CompleteMertensPeak.U and M is firstLiMass. One nonnegative constant C and one real threshold serve every larger real x. The second correction uses the logarithm of the logarithm.

Put y = log x and q = exp(−y/2). For every amplitude b between zero and one half, the step t = byq satisfies t ≤ 1/2 and yt ≤ 1 on a tail independent of b. ActualKernelCusp.cusp_remainder_bound bounds the quadratic remainder by 2t². Expanding log t gives the common cusp lower bound. A second-order estimate for the two exponentials at the midpoint makes its error at most qby.

For N equally spaced phases the ordered-pair amplitudes are |j−k|/(2N). Their mean is (1−1/N²)/6 and their mean square is (1−1/N²)/24. The positive Fejér phase comparison then gives the factor 1−1/N² on the quadratic and logarithmic terms. With y fixed on the common tail, send N to infinity. The remaining linear and constant errors are absorbed by C log x.

In reverse, log(y)/y and 1/y tend to zero. The two corrections are eventually smaller than the margin for any fixed coefficient below 1/48. MangoldtFejerGap.rh_iff_eventually_fejer_gap gives RH. The derivation is at https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7070606425.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtUniformFejerGap.rh_iff_eventually_uniform_fejer_gap`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerGap](MangoldtFejerGap.md)
