# Archimedean Divergence of Translated Packets

## Abstract

This is the Archimedean half of the zero-infinitude argument in Addendum Thirty, stated for an abstract profile H. A later module instantiates H with the cosine packet.

Growth comes from the frozen Stirling bound mu_stirling and monotonicity of mu on the nonnegative real axis. The quantified lower bound is the escape witness that connects those facts to translated packet mass.

This module is not a proof of the Riemann hypothesis and makes no statement about zeros.

**Definition 1.1 (The translated packet).**

$$\forall H \in \mathbb{R} \to \mathbb{R}, T \in \mathbb{R}, r \in \mathbb{R},\; \operatorname{packet}\left(H, T, r\right) = \frac{H\left(r + T\right) + H\left(r - T\right)}{2}$$

*Formalization.* `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.packet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The packet is the symmetric average of the two opposite translations of H.

**Theorem 1.2 (Translation preserves packet mass).**

$$\forall H \in \mathbb{R} \to \mathbb{R},\; \operatorname{Integrable}\left(H\right) \Rightarrow \left(\forall T \in \mathbb{R},\; \int_{\mathbb{R}} \operatorname{packet}\left(H, T, r\right) dr = \int_{\mathbb{R}} H\left(r\right) dr\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.packet_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Translation invariance of Lebesgue integration makes the average retain the total integral of H.

**Theorem 1.3 (The shifted Archimedean weight is positive).**

$$\forall r \in \mathbb{R},\; 0 < \operatorname{mu}\left(r\right) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.mu_add_one_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen global lower bound for mu combines with its strict value at zero to give positivity after adding one.

**Theorem 1.4 (The Archimedean weight tends to infinity).**

$$\operatorname{Tendsto}\left((r: \mathbb{R} \mapsto \operatorname{mu}\left(r\right)), atTop, atTop\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.mu_tendsto_atTop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen Stirling estimate bounds mu below by its logarithmic main term minus a constant.

**Theorem 1.5 (Quadratic decay makes the weighted packet integrable).**

$$\forall H \in \mathbb{R} \to \mathbb{R}, K \in \mathbb{R}, T \in \mathbb{R},\; \left(\left(\operatorname{Integrable}\left(H\right) \land 0 \le K\right) \land \left(\forall x \in \mathbb{R},\; \left|H\left(x\right)\right| \le \frac{K}{1 + x^{2}}\right)\right) \Rightarrow \operatorname{Integrable}\left((r: \mathbb{R} \mapsto \operatorname{packet}\left(H, T, r\right) \cdot \operatorname{mu}\left(r\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.packet_weighted_integrable_of_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quadratic decay is stable under each fixed translation and dominates the logarithmic growth of mu by an integrable power tail.

**Theorem 1.6 (A translated interval gives the escape lower bound).**

$$\forall H \in \mathbb{R} \to \mathbb{R}, delta \in \mathbb{R}, K \in \mathbb{R}, T \in \mathbb{R},\; \left(\left(\left(\left(\left(\left(\operatorname{Integrable}\left(H\right) \land \left(\forall r \in \mathbb{R},\; 0 \le H\left(r\right)\right)\right) \land 0 < delta\right) \land \left(\forall t \in \mathbb{R},\; \left|t\right| \le delta \Rightarrow \frac{1}{2} \le H\left(t\right)\right)\right) \land 0 \le K\right) \land \left(\forall x \in \mathbb{R},\; \left|H\left(x\right)\right| \le \frac{K}{1 + x^{2}}\right)\right) \land delta \le T\right) \Rightarrow \frac{delta}{2} \cdot \left(\operatorname{mu}\left(T - delta\right) + 1\right) - \int_{\mathbb{R}} H\left(r\right) dr \le \int_{\mathbb{R}} \operatorname{packet}\left(H, T, r\right) \cdot \operatorname{mu}\left(r\right) dr$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.archimedean_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the profile's integrability, nonnegativity, local lower bound, and quadratic decay hypotheses, the weighted packet is integrable. On the interval from T-delta to T+delta, one translated copy contributes at least one half and the other remains nonnegative. Monotonicity of mu then yields the displayed delta-over-two lower bound.

**Theorem 1.7 (The real weighted packet integral diverges).**

$$\forall H \in \mathbb{R} \to \mathbb{R}, delta \in \mathbb{R}, K \in \mathbb{R},\; \left(\left(\left(\left(\left(\operatorname{Integrable}\left(H\right) \land \left(\forall r \in \mathbb{R},\; 0 \le H\left(r\right)\right)\right) \land 0 < delta\right) \land \left(\forall t \in \mathbb{R},\; \left|t\right| \le delta \Rightarrow \frac{1}{2} \le H\left(t\right)\right)\right) \land 0 \le K\right) \land \left(\forall x \in \mathbb{R},\; \left|H\left(x\right)\right| \le \frac{K}{1 + x^{2}}\right)\right) \Rightarrow \operatorname{Tendsto}\left((T: \mathbb{R} \mapsto \int_{\mathbb{R}} \operatorname{packet}\left(H, T, r\right) \cdot \operatorname{mu}\left(r\right) dr), atTop, atTop\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.archimedean_divergence_of_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The escape lower bound and the logarithmic growth of mu force the real weighted integral to positive infinity.

**Theorem 1.8 (The real part of the complex integral diverges).**

$$\forall H \in \mathbb{R} \to \mathbb{R}, delta \in \mathbb{R}, K \in \mathbb{R},\; \left(\left(\left(\left(\left(\operatorname{Integrable}\left(H\right) \land \left(\forall r \in \mathbb{R},\; 0 \le H\left(r\right)\right)\right) \land 0 < delta\right) \land \left(\forall t \in \mathbb{R},\; \left|t\right| \le delta \Rightarrow \frac{1}{2} \le H\left(t\right)\right)\right) \land 0 \le K\right) \land \left(\forall x \in \mathbb{R},\; \left|H\left(x\right)\right| \le \frac{K}{1 + x^{2}}\right)\right) \Rightarrow \operatorname{Tendsto}\left((T: \mathbb{R} \mapsto \Re(\int_{\mathbb{R}} {\operatorname{packet}\left(H, T, r\right): \mathbb{C}} \cdot {\operatorname{mu}\left(r\right): \mathbb{C}} dr)), atTop, atTop\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.archimedean_divergence_complex_of_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complexification preserves the real integrand, so taking the real part recovers the real divergence statement exactly.

**Theorem 1.9 (The explicit-formula gamma term is the packet integral).**

$$\forall k \in \mathbb{R} \to \mathbb{C}, H \in \mathbb{R} \to \mathbb{R}, T \in \mathbb{R},\; \left(\forall r \in \mathbb{R},\; \operatorname{paperFT}\left(k, r\right) = {\operatorname{packet}\left(H, T, r\right): \mathbb{C}}\right) \Rightarrow {\frac{1}{2 \cdot \pi}: \mathbb{C}} \cdot \int_{\mathbb{R}} \operatorname{paperFT}\left(k, r\right) \cdot {\operatorname{gammaBracket}\left(r\right): \mathbb{C}} dr = \int_{\mathbb{R}} {\operatorname{packet}\left(H, T, r\right): \mathbb{C}} \cdot {\operatorname{mu}\left(r\right): \mathbb{C}} dr$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.gamma_term_packet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen gamma_term identity rewrites the explicit-formula density, and the supplied pointwise paper-transform identity replaces it by the translated packet.

## References

- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.archimedean_divergence_complex_of_decay`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.archimedean_divergence_of_decay`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.archimedean_lower_bound`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.gamma_term_packet`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.mu_add_one_pos`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.mu_tendsto_atTop`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.packet`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.packet_integral`
- Truth anchor: `D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.packet_weighted_integrable_of_decay`
