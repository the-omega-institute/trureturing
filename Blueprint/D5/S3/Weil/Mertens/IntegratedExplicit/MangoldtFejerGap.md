# A family of midpoint inequalities

## Abstract

Finite Fejér averages for the integrated Mangoldt remainder

**Theorem 1.1 (A squared-logarithm saving for every coefficient below one forty-eighth).**

$$\operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall c \in \mathbb{R},\; c < \frac{1}{48} \Rightarrow \left(\exists T \in \mathbb{R},\; \forall x \in \mathbb{R},\; T \le x \Rightarrow \operatorname{U}\left(x\right) \le firstLiMass \cdot \sqrt{x} - c \cdot \operatorname{log}\left(x\right)^{2}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerGap.rh_iff_eventually_fejer_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here U is CompleteMertensPeak.U and M is firstLiMass. For each real c below 1/48, the threshold may depend on c. The estimate holds for all real x past it.

Write y = log x, q = exp(−y/2), and d(t) = M − K(t). Use the N equally spaced phases indexed by j from 0 to N−1. The sum of cos((j−k)θ) over all ordered pairs is the squared modulus of the sum of their complex exponentials, by the frozen FejerNearCollisionBound pair-cosine identity. Under RH the spectral weights are positive. The square therefore bounds the combined midpoint defects in terms of the same central deficit d(y).

For each pair take the step byq with b = |j−k|/(2N). After division by qy², the cusp term tends to b/2 and the arithmetic curvature contributes at most b². The explicit-formula residual vanishes at this scale. Summing the first and second distance moments gives the coefficient (1−1/N²)/48.

For c below 1/48, choose a finite N with c below this coefficient before taking the real tail. For the converse, restrict the coefficients to c below 1/64 and apply MangoldtLogSquareGap.rh_iff_eventually_log_squared_gap. Its converse uses c = 1/128 to force divergence of the critical gap. The source derivation is at https://github.com/the-omega-institute/trureturing/issues/32551#issuecomment-7070009503.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtFejerGap.rh_iff_eventually_fejer_gap`
- Dependency: [D5/S1/Phase/Interference/DedekindReciprocityFiniteSums](../../../../S1/Phase/Interference/DedekindReciprocityFiniteSums.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtLogSquareGap](MangoldtLogSquareGap.md)
- Dependency: [D5/S3/Zeros/Repulsion/FejerNearCollisionBound](../../../Zeros/Repulsion/FejerNearCollisionBound.md)
