# Exchange Rate Composition

## Abstract

Exchange rates multiply when normal translations compose.

**Proposition 1.1 (Exchange rates multiply under normal composition).**

$$\operatorname{limitAlong}\left(\mathit{lA}, \operatorname{ratio}\left(\operatorname{h0}\left(a\right), \operatorname{h2}\left(\operatorname{tau2}\left(\operatorname{tau1}\left(a\right)\right)\right)\right)\right) = \mathit{rho1} \cdot \mathit{rho2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/ExchangeRateComposition.exchange_rate_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source and intermediate filters represent the declared high-resource domains of the two translations, and a target filter records the target domain. Normality sends the first filter to the intermediate filter and the intermediate filter to the target filter; total maps encode the source domain and composite-domain conditions.

The first rate is the source-to-intermediate height ratio. The second rate is the intermediate-to-target ratio, and normality transports that limit along the first translation. Intermediate height tending to infinity makes the shared factor eventually nonzero, so cancellation identifies the product of the two ratios with the composite ratio.

Pinned Mathlib supplies Tendsto.comp, Tendsto.mul, Tendsto.eventually_gt_atTop, and div_mul_div_cancel_0. No complete exchange-rate composition theorem was found, so the Lean declaration is a thin assembly of those upstream facts.

## References

- Truth anchor: `D5/S0/Naming/ExchangeRateComposition.exchange_rate_composition`
