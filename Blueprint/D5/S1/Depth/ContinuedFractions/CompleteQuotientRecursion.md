# Quadratic Invariants Along Complete Quotients

## Abstract

Inverse-step pullbacks make successive quadratic coefficients cross over while preserving one discriminant throughout the complete-quotient chain.

**Lemma 1.1 (The next constant coefficient is the current leading coefficient).**

$$\forall x \in \mathbb{R}, C: \operatorname{QuadraticChain}\left(x\right), \forall n \in \mathbb{N},\ \operatorname{constant}\left(\operatorname{coefficients}\left(C, n + 1\right)\right) = \operatorname{leading}\left(\operatorname{coefficients}\left(C, n\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion.next_constant_eq_current_leading` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pulling the current quadratic equation back through the inverse continued-fraction step places its leading coefficient in the constant position of the next equation. This crossover holds at every stage of a compatible quadratic chain.

**Lemma 1.2 (Every chain equation has the initial discriminant).**

$$\forall x \in \mathbb{R}, C: \operatorname{QuadraticChain}\left(x\right), \forall n \in \mathbb{N},\ \operatorname{discriminant}\left(\operatorname{coefficients}\left(C, n\right)\right) = \operatorname{discriminant}\left(\operatorname{coefficients}\left(C, 0\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion.quadratic_chain_discriminant_eq_initial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse-step Mobius transformation has determinant minus one. A pullback scales the discriminant by the determinant squared, so each recurrence step preserves it; induction identifies every stage with the discriminant of the initial equation.

**Theorem 1.3 (Quadratic chains share coefficient and discriminant invariants).**

$$\forall x \in \mathbb{R}, C: \operatorname{QuadraticChain}\left(x\right),\ (\forall n \in \mathbb{N}, \operatorname{constant}\left(\operatorname{coefficients}\left(C, n + 1\right)\right) = \operatorname{leading}\left(\operatorname{coefficients}\left(C, n\right)\right)) \land (\exists D \in \mathbb{Z}, \forall n \in \mathbb{N}, \operatorname{discriminant}\left(\operatorname{coefficients}\left(C, n\right)\right) = D).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion.complete_quotient_quadratic_chain_invariants` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every compatible quadratic chain simultaneously has the coefficient crossover at each successor stage and one integral discriminant shared by all its equations. The common value may be chosen as the discriminant of the initial coefficient triple.

The result packages invariants of a supplied chain; it does not assert that such a chain exists for every real number.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion.complete_quotient_quadratic_chain_invariants`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion.next_constant_eq_current_leading`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/CompleteQuotientRecursion.quadratic_chain_discriminant_eq_initial`
- Dependency: [D5/S1/Depth/ContinuedFractions/CompleteQuotientBound](CompleteQuotientBound.md)
- Dependency: [D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic](QuadraticImpliesPeriodic.md)
