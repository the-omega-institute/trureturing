# Primitive-generator comparison arithmetic

## Abstract

The rational arithmetic core of the primitive-generator versus double-anchor count comparison.

**Theorem 1.1 (The explicit comparison count is strictly reduced).**

$$\forall n \in \mathbb{Q},\; \forall m \in \mathbb{Q},\; \forall d \in \mathbb{Q},\; \left(4 \le n \land \left(n \le m \land \left(m \le n + 2 \land \frac{n \cdot n + 1}{2} \le d\right)\right)\right) \Rightarrow \left(n - 2 \cdot d - \frac{n \cdot n + 1}{2} \le \operatorname{generatorComparisonCount}\left(m, d\right) - \operatorname{pairComparisonCount}\left(d\right) \land \left(\frac{n \cdot n + 1 \cdot n - 3}{2} \le \operatorname{generatorComparisonCount}\left(m, d\right) - \operatorname{pairComparisonCount}\left(d\right) \land 0 < \operatorname{generatorComparisonCount}\left(m, d\right) - \operatorname{pairComparisonCount}\left(d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/PrimitiveGeneratorComparisonArithmetic.explicit_comparison_strict_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For rational n, m and d with n at least four, a generating prefix between n and n plus two, and d at least n(n plus one)/2, the generator count md minus m(m plus one)/2 dominates the two-anchor count 2d. The theorem proves both displayed lower bounds and strict positivity. It formalizes the arithmetic comparison only; it does not formalize the Euclidean Jordan algebra generator theorem.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Representation/PrimitiveGeneratorComparisonArithmetic.explicit_comparison_strict_reduction`
