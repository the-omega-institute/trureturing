# Dual Number Multiplicativity Criterion

## Abstract

The canonical dual-number lift is multiplicative exactly under the product rule.

**Theorem 1.1 (Multiplicativity is equivalent to the product rule).**

$$\begin{gathered}\forall R, A: \operatorname{Type}, D: A \to A,\\{}\operatorname{CommSemiring}(R) \land \operatorname{Semiring}(A) \land \operatorname{Algebra}(R, A) \land \operatorname{LinearMap}(R, D, A, A) \Rightarrow\\{}(\forall a, b: A, (\operatorname{inl}(a \cdot b) + \operatorname{inr}(D(a \cdot b))) = (\operatorname{inl}(a) + \operatorname{inr}(D(a))) \cdot (\operatorname{inl}(b) + \operatorname{inr}(D(b)))) \iff (\forall a, b: A, D(a \cdot b) = a \cdot D(b) + D(a) \cdot b).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Algebra/DualNumberMultiplicativityCriterion.dual_number_lift_preserves_mul_iff_product_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be an algebra over a commutative scalar semiring R, and let D : A -> A be R-linear.

The displayed map uses the canonical inclusions into the square-zero extension. It preserves products exactly when D obeys the displayed left-right product rule.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Algebra/DualNumberMultiplicativityCriterion.dual_number_lift_preserves_mul_iff_product_rule`
