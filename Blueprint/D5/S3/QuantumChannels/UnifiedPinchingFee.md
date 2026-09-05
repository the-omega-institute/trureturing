# Unified Pinching Fee

## Abstract

A binary-entropy pinching fee has one transition profile joining its pure- and mixed-state asymptotics.

**Lemma 1.1 (The singular boundary remainder vanishes).**

$$\forall x: \mathbb{R}, 0 \leq x \Rightarrow \operatorname{Tendsto}\left((t: \mathbb{R} \mapsto \frac{\operatorname{negMulLog}\left(\operatorname{boundaryUpperProbability}\left(t, x\right)\right) - \operatorname{negMulLog}\left(t \cdot x\right)}{t} - {\operatorname{log}\left(t^{-1}\right) + x \cdot \operatorname{log}\left(x\right) - {x + 1} \cdot \operatorname{log}\left(x + 1\right)}), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(0\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/UnifiedPinchingFee.singular_boundary_error_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every nonnegative transition coordinate x, the singular part of the binary-entropy increment differs from its explicit logarithmic profile by a quantity tending to zero as the scale tends to zero from above.

This is the analytic remainder estimate used on the live derivation path. It follows from continuity of y log y at zero and a first-order calculation for the boundary eigenvalue.

**Theorem 1.2 (The unified pinching-fee law).**

$$\begin{aligned}\forall x: \mathbb{R}, r: \mathbb{R}, 0 \leq x \land 0 < r \land r < 1 \Rightarrow\\{}\operatorname{Tendsto}\left((t: \mathbb{R} \mapsto \frac{\operatorname{boundaryPinchingFee}\left(t, x\right)}{t \cdot \operatorname{transitionLeading}\left(t, x\right)}), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(1\right)\right) \land\\{}\operatorname{Tendsto}\left(transitionCorrection, \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(1\right)\right) \land\\{}\operatorname{Tendsto}\left((y: \mathbb{R} \mapsto \operatorname{transitionLeading}\left(\frac{\operatorname{doorGap}\left(r\right)}{2 \cdot y}, y\right)), atTop, \operatorname{nhds}\left(\operatorname{log}\left(\frac{2}{\operatorname{doorGap}\left(r\right)}\right)\right)\right) \land\\{}\operatorname{Tendsto}\left((delta: \mathbb{R} \mapsto \frac{\operatorname{quadraticPinchingFee}\left(r, \operatorname{handTremor}\left(delta\right)\right)}{delta^{2}}), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(\frac{r \cdot \operatorname{artanh}\left(r\right)}{2}\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/UnifiedPinchingFee.unified_pinching_fee_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let t = delta squared over four, u = 1-r, and x = u/(2t). These source coordinates are the public definitions handTremor, doorGap, and transitionCoordinate. The fee is the exact binary-entropy increment quadraticPinchingFee, not a function defined by the target asymptotic.

Along r = 1-2tx, the quotient of the exact fee by t times the displayed transition coefficient tends to one. The scale-independent correction tends to one at x approaching zero from above, giving the pure-state logarithmic law.

At the mixed-state end, substituting t = u/(2x) makes the transition coefficient tend to log(2/u). For fixed 0<r<1 and t=delta squared over four, the fee divided by delta squared tends to r artanh(r)/2.

The source's numerical crossover ratio 1.0000 to 0.9946 is an empirical remark and is outside this theorem.

## References

- Truth anchor: `D5/S3/QuantumChannels/UnifiedPinchingFee.singular_boundary_error_limit`
- Truth anchor: `D5/S3/QuantumChannels/UnifiedPinchingFee.unified_pinching_fee_law`
