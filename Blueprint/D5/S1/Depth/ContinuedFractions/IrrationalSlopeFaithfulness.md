# Irrational Slope Faithfulness

## Abstract

Irrational slopes faithfully encode integer pairs; the golden encoding also separates bounded-denominator labels by an effective finite-precision gap.

**Definition 1.1 (The slope encoding).**

$$E_{\alpha} : \mathbb{Z}^{2} \to \mathbb{R},\ E_{\alpha}(m,n) = \alpha \cdot m + n$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.slopeEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real slope alpha, the encoding sends the integer label (m,n) to alpha times m plus n. This is the E_alpha used in the theorem; its carrier is the actual product of two integer copies, not a finite enumeration or an abstract replacement.

**Definition 1.2 (Rational approximations as integer labels).**

$$ell_{q} = (\operatorname{den}(q), -\operatorname{num}(q))$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.rationalApproximationLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A reduced rational q supplies the primitive integer label (den(q), -num(q)). Its golden slope encoding is the unnormalized separation den(q) times (phi - q).

**Definition 1.3 (The effective finite-precision gap).**

$$g(P) = \frac{1}{\sqrt{5} P + 1}$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.finitePrecisionGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At precision P, the visible separation threshold is 1/(sqrt(5) P + 1). It decreases as the denominator budget grows.

**Definition 1.4 (Finite-precision stability observes the encoding).**

$$\operatorname{FinitePrecisionStable}(F) \iff \forall P \in \mathbb{N},\ 0 < P \Rightarrow \forall q \in \mathbb{Q},\ \operatorname{den}(q) \leq P \Rightarrow g(P) < |F(ell_{q})|$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.FinitePrecisionStable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive precision P and rational q with denominator at most P, the actual encoded primitive label must remain farther from zero than the precision-dependent gap. A constant encoding fails this property.

**Definition 1.5 (The golden Hurwitz certificate is tied to the golden encoding).**

$$\operatorname{GoldenFinitePrecisionStability} \iff ((\forall q \in \mathbb{Q},\ \frac{1}{\sqrt{5}\,\operatorname{den}(q)^{2} + \operatorname{den}(q)} < |\varphi - q|) \land \operatorname{FinitePrecisionStable}(E_{\varphi}))$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.GoldenFinitePrecisionStability` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This package preserves the prior rational Hurwitz bound and also carries its finite-precision interpretation for the actual map E_phi. The second field is the separation bridge absent from the earlier type.

**Theorem 1.6 (Every irrational slope is faithful).**

$$\forall \alpha \in \mathbb{R},\ \operatorname{Irrational}(\alpha) \Rightarrow (\operatorname{Injective}(E_{\alpha}) \land (\forall \beta \in \mathbb{R},\ \operatorname{Irrational}(\beta) \Rightarrow \operatorname{Injective}(E_{\beta})) \land (\exists \beta \in \mathbb{R},\ \beta \neq \varphi \land \operatorname{Irrational}(\beta) \land \operatorname{Injective}(E_{\beta})) \land \operatorname{GoldenFinitePrecisionStability})$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.irrational_slope_faithfulness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four displayed clauses mirror the four statement-level claims. The first gives injectivity at the fixed irrational slope. The second quantifies the same faithfulness over every irrational slope. The third supplies a faithful irrational slope distinct from the golden ratio, so golden faithfulness is not unique. The fourth is the golden finite-precision package: it preserves the Hurwitz inequality and applies it to encoded labels at every explicit denominator precision.

For injectivity, equality of two encoded labels gives alpha times the difference of their first coordinates equal to an integer. A nonzero first-coordinate difference would make that product irrational, a contradiction. The remaining integer coordinates then agree. The golden conjugate is the distinct faithful witness, and the existing golden Hurwitz theorem yields a positive encoded separation after scaling by each rational denominator.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.FinitePrecisionStable`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.GoldenFinitePrecisionStability`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.finitePrecisionGap`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.irrational_slope_faithfulness`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.rationalApproximationLabel`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.slopeEncoding`
- Dependency: [D5/S1/Depth/GoldenHurwitzBound](../GoldenHurwitzBound.md)
