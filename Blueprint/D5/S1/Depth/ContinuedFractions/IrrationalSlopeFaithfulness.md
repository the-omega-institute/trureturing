# Irrational Slope Faithfulness

## Abstract

Irrational slopes faithfully encode integer pairs; the golden encoding also separates distinct labels within a finite horizontal precision budget.

**Definition 1.1 (The slope encoding).**

$$E_{\alpha} : \mathbb{Z}^{2} \to \mathbb{R},\ E_{\alpha}(m,n) = \alpha \cdot m + n$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.slopeEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real slope alpha, the encoding sends the integer label (m,n) to alpha times m plus n. This is the E_alpha used in the theorem; its carrier is the actual product of two integer copies, not a finite enumeration or an abstract replacement.

**Definition 1.2 (The effective finite-precision gap).**

$$g(P) = \frac{1}{\sqrt{5} P + 1}$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.finitePrecisionGap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At precision P, the visible separation threshold is 1/(sqrt(5) P + 1). It decreases as the horizontal budget grows.

**Definition 1.3 (Finite-precision stability observes the encoding).**

$$\operatorname{FinitePrecisionStable}(F) \iff \forall P \in \mathbb{N},\ 0 < P \Rightarrow \forall x, y \in \mathbb{Z}^{2},\ |x_{1} - y_{1}| \leq P \Rightarrow x \neq y \Rightarrow g(P) < |F(x) - F(y)|$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.FinitePrecisionStable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every positive precision P, any two distinct integer-pair labels whose first-coordinate displacement is at most P must have encoded outputs separated by more than the precision-dependent gap. Thus even a nonzero constant encoding fails this property.

**Theorem 1.4 (Every irrational slope is faithful).**

$$\forall \alpha \in \mathbb{R},\ \operatorname{Irrational}(\alpha) \Rightarrow (\operatorname{Injective}(E_{\alpha}) \land (\forall \beta \in \mathbb{R},\ \operatorname{Irrational}(\beta) \Rightarrow \operatorname{Injective}(E_{\beta})) \land (\exists \beta \in \mathbb{R},\ \beta \neq \varphi \land \operatorname{Irrational}(\beta) \land \operatorname{Injective}(E_{\beta})) \land \operatorname{FinitePrecisionStable}(E_{\varphi}))$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.irrational_slope_faithfulness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four displayed clauses mirror the four statement-level claims. The first gives injectivity at the fixed irrational slope. The second quantifies the same faithfulness over every irrational slope. The third supplies a faithful irrational slope distinct from the golden ratio, so golden faithfulness is not unique. The fourth directly asserts pairwise finite-precision stability of the golden encoding; it contains no additional public Hurwitz assertion.

For injectivity, equality of two encoded labels gives alpha times the difference of their first coordinates equal to an integer. A nonzero first-coordinate difference would make that product irrational, a contradiction. The remaining integer coordinates then agree. The golden conjugate is the distinct faithful witness, and the existing golden Hurwitz theorem supplies the arithmetic estimate used internally to prove the pairwise output gap.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.FinitePrecisionStable`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.finitePrecisionGap`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.irrational_slope_faithfulness`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/IrrationalSlopeFaithfulness.slopeEncoding`
- Dependency: [D5/S1/Depth/GoldenHurwitzBound](../GoldenHurwitzBound.md)
