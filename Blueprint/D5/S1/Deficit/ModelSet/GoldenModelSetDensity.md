# Density of the Golden Model Set

## Abstract

Golden model-set prefixes are exact half-open endpoint windows, and their counts have asymptotic density one over square root five.

**Lemma 1.1 (The expanding coordinate stays within one unit of its linear scale).**

$$\forall v \in \mathbb{N},\; \left|\operatorname{betaReal}\left(v\right) - v \cdot \sqrt{5}\right| < 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_real_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural parameter v, the real embedding of its golden beta point differs from v times square root five by less than one. The Beatty-floor closed form confines the floor error to one unit, while the golden-ratio bounds place the remaining offset in the same open interval.

**Lemma 1.2 (The expanding coordinate is strictly increasing).**

$$\operatorname{StrictMono}\left(\mathit{betaReal}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_real_strictMono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Advancing the natural parameter by at least one increases the linear main term by at least square root five. Since square root five exceeds two, the two one-unit error bounds cannot erase that increase, so betaReal is strictly increasing.

**Lemma 1.3 (The golden beta parameterization is injective).**

$$\operatorname{Injective}\left(\mathit{betaGolden}\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_golden_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The second integer coordinate of a golden beta point records its natural parameter. Equal beta points therefore have equal recorded parameters, so two distinct natural indices cannot name the same model-set point.

**Lemma 1.4 (The expanding coordinate starts at zero).**

$$\operatorname{betaReal}\left(0\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_real_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The floor of the golden ratio is one. Substituting this initial Beatty value into the displacement and conjugate closed form shows that the expanding coordinate of the zeroth golden beta point is exactly the origin.

**Lemma 1.5 (Each golden prefix has its index as cardinality).**

$$\forall n \in \mathbb{N},\; \operatorname{card}\left(\operatorname{goldenPrefix}\left(n\right)\right) = n$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.golden_prefix_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix of length n is the image of the first n natural parameters under the injective golden beta map. No points collide, so taking the image preserves the n-element cardinality of the parameter range.

**Lemma 1.6 (A golden prefix is exactly its half-open endpoint window).**

$$\forall n \in \mathbb{N},\; \forall x \in \operatorname{GoldenInt},\; x \in \operatorname{goldenPrefix}\left(n\right) \Leftrightarrow \left(x \in \mathit{goldenModelSet} \land \left(0 \le \operatorname{embedding}\left(x\right) \land \operatorname{embedding}\left(x\right) < \operatorname{betaReal}\left(n\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.mem_golden_prefix_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A golden integer lies in the first n beta points exactly when it belongs to the golden model set and its expanding coordinate lies from zero inclusive to betaReal n exclusive. Strict monotonicity orders the model-set points by their canonical natural parameters, and the zeroth coordinate supplies the lower endpoint.

**Lemma 1.7 (The endpoint scale tends to square root five).**

$$\operatorname{Tendsto}\left(\frac{\operatorname{betaReal}\left(n\right)}{n}, \mathit{atTop}, \operatorname{nhds}\left(\sqrt{5}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_real_ratio_tendsto` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Dividing the uniform one-unit error estimate by a positive parameter traps betaReal n over n between square root five minus one over n and square root five plus one over n. Both bounds have the same limit, so the endpoint scale converges to square root five.

**Theorem 1.8 (The golden model set has density one over square root five).**

$$\left(\forall n \in \mathbb{N},\; \operatorname{card}\left(\operatorname{goldenPrefix}\left(n\right)\right) = n \land \left(\forall x \in \operatorname{GoldenInt},\; x \in \operatorname{goldenPrefix}\left(n\right) \Leftrightarrow \left(x \in \mathit{goldenModelSet} \land \left(0 \le \operatorname{embedding}\left(x\right) \land \operatorname{embedding}\left(x\right) < \operatorname{betaReal}\left(n\right)\right)\right)\right)\right) \land \operatorname{Tendsto}\left(\frac{\operatorname{card}\left(\operatorname{goldenPrefix}\left(n\right)\right)}{\operatorname{betaReal}\left(n\right)}, \mathit{atTop}, \operatorname{nhds}\left(\frac{1}{\sqrt{5}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.golden_model_set_density` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every endpoint betaReal n, the corresponding half-open window contains exactly the first n golden model-set points and therefore has count n. This identifies the finite counting sets rather than only estimating their sizes.

The count-to-endpoint ratio is n divided by betaReal n. Inverting the endpoint-scale limit, whose positive limit is square root five, gives the asymptotic density one over square root five along these exact model-set endpoints.

## References

- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_golden_injective`
- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_real_error`
- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_real_ratio_tendsto`
- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_real_strictMono`
- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.beta_real_zero`
- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.golden_model_set_density`
- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.golden_prefix_card`
- Truth anchor: `D5/S1/Deficit/ModelSet/GoldenModelSetDensity.mem_golden_prefix_iff`
- Dependency: [D5/S1/Deficit/Beatty/BetaBeattyClosedForms](../Beatty/BetaBeattyClosedForms.md)
- Dependency: [D5/S1/Deficit/ModelSet/GoldenModelSetSelfSimilar](GoldenModelSetSelfSimilar.md)
