# Irrational Slope Faithfulness

## Abstract

Irrational slopes faithfully encode integer pairs, while the golden slope also has an effective finite-precision gap.

**Definition 1.1 (The slope encoding).**

$$E_{\alpha} : \mathbb{Z}^{2} \to \mathbb{R},\ E_{\alpha}(m,n) = \alpha \cdot m + n$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.slopeEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real slope alpha, the encoding sends the integer label (m,n) to alpha times m plus n. This is the E_alpha used in the theorem; its carrier is the actual product of two integer copies, not a finite enumeration or an abstract replacement.

**Theorem 1.2 (Every irrational slope is faithful).**

$$\forall \alpha \in \mathbb{R},\ \operatorname{Irrational}(\alpha) \Rightarrow (\operatorname{Injective}(E_{\alpha}) \land (\forall \beta \in \mathbb{R},\ \operatorname{Irrational}(\beta) \Rightarrow \operatorname{Injective}(E_{\beta})) \land (\exists \beta \in \mathbb{R},\ \beta \neq \varphi \land \operatorname{Irrational}(\beta) \land \operatorname{Injective}(E_{\beta})) \land (\forall q \in \mathbb{Q},\ \frac{1}{\sqrt{5}\,\operatorname{den}(q)^{2} + \operatorname{den}(q)} < |\varphi - q|))$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.irrational_slope_faithfulness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four displayed clauses mirror the four statement-level claims. The first gives injectivity at the fixed irrational slope. The second quantifies the same faithfulness over every irrational slope. The third supplies a faithful irrational slope distinct from the golden ratio, so golden faithfulness is not unique. The fourth records the effective Hurwitz separation inequality that carries the golden ratio's additional finite-precision stability.

For injectivity, equality of two encoded labels gives alpha times the difference of their first coordinates equal to an integer. A nonzero first-coordinate difference would make that product irrational, a contradiction. The remaining integer coordinates then agree. The golden conjugate is the distinct faithful witness, and the final clause is applied directly from the existing golden Hurwitz theorem.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.irrational_slope_faithfulness`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.slopeEncoding`
- Dependency: [D5/S1/Depth/GoldenHurwitzBound](../GoldenHurwitzBound.md)
