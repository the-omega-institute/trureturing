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

$$\begin{aligned}{}(\forall x: \mathbb{R}, 0 \leq x \Rightarrow \operatorname{Tendsto}\left((t: \mathbb{R} \mapsto \frac{\operatorname{boundaryPinchingFee}\left(t, x\right)}{t \cdot \operatorname{transitionLeading}\left(t, x\right)}), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(1\right)\right)) \land\\{}\operatorname{Tendsto}\left(transitionCorrection, \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(1\right)\right) \land\\{}(\forall r: \mathbb{R}, r < 1 \Rightarrow \operatorname{Tendsto}\left((y: \mathbb{R} \mapsto \operatorname{transitionLeading}\left(\frac{\operatorname{doorGap}\left(r\right)}{2 \cdot y}, y\right)), atTop, \operatorname{nhds}\left(\operatorname{log}\left(\frac{2}{\operatorname{doorGap}\left(r\right)}\right)\right)\right)) \land\\{}(\forall r: \mathbb{R}, 0 < r \Rightarrow r < 1 \Rightarrow \operatorname{Tendsto}\left((delta: \mathbb{R} \mapsto \frac{\operatorname{quadraticPinchingFee}\left(r, \operatorname{handTremor}\left(delta\right)\right)}{delta^{2}}), \operatorname{nhdsWithin}\left(0, \operatorname{Ioi}\left(0\right)\right), \operatorname{nhds}\left(\frac{r \cdot \operatorname{artanh}\left(r\right)}{2}\right)\right)) \land\\{}\operatorname{Tendsto}\left((r: \mathbb{R} \mapsto \frac{2 \cdot r \cdot \operatorname{artanh}\left(r\right)}{\operatorname{log}\left(\frac{2}{1 - r}\right)}), \operatorname{nhdsWithin}\left(1, \operatorname{Iio}\left(1\right)\right), \operatorname{nhds}\left(1\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumChannels/UnifiedPinchingFee.unified_pinching_fee_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source scales t = delta squared over four and u = 1-r are exposed by handTremor and doorGap. The relation r = 1-2tx is exposed by boundaryRadius, while the third conjunct uses its inverse substitution t = doorGap(r)/(2x). The fee is the exact binary-entropy increment quadraticPinchingFee, not a function defined by the target asymptotic.

Along r = 1-2tx, the quotient of the exact fee by t times the displayed transition coefficient tends to one. The scale-independent correction tends to one at x approaching zero from above, giving the pure-state logarithmic law.

At the mixed-state end, substituting t = u/(2x) makes the transition coefficient tend to log(2/u). For fixed 0<r<1 and t=delta squared over four, the fee divided by delta squared tends to r artanh(r)/2; this fourth limit is the formal first-order content. The fixed-x fee ratio and the x-to-infinity profile formalize separate regimes and are not composed into a single limit.

The source's 'that is' bridge is carried in the gate-closing regime: as r approaches one from below, the ratio of 2r artanh(r) to log(2/(1-r)) tends to one. The coefficients are not asserted equal at a fixed mixed-state radius.

The source sentence reporting a numerical crossover ratio from 1.0000 to 0.9946 is computational-experiment content and is not formalized.

## References

- Truth anchor: `D5/S3/QuantumChannels/UnifiedPinchingFee.singular_boundary_error_limit`
- Truth anchor: `D5/S3/QuantumChannels/UnifiedPinchingFee.unified_pinching_fee_law`
