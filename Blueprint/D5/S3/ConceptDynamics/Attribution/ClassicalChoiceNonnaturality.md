# Classical-Choice Nonnaturality

## Abstract

Classical choice supplies finite selectors, but the resulting family is not natural.

**Theorem 1.1 (The classical-choice family is not natural).**

$$\begin{aligned}\operatorname{let} choice: \forall alpha: Type, f: \operatorname{Fintype}\left(alpha\right), h: \operatorname{Nonempty}\left(alpha\right), alpha := (alpha, f, h) \mapsto \operatorname{ClassicalChoice}\left(h\right),\\\neg \forall alpha, beta: Type, fAlpha: \operatorname{Fintype}\left(alpha\right), fBeta: \operatorname{Fintype}\left(beta\right), hAlpha: \operatorname{Nonempty}\left(alpha\right), hBeta: \operatorname{Nonempty}\left(beta\right), e: \operatorname{Equiv}\left(alpha, beta\right), e\left(choice\left(alpha, fAlpha, hAlpha\right)\right) = choice\left(beta, fBeta, hBeta\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ClassicalChoiceNonnaturality.classical_choice_family_is_nonnatural` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each finite nonempty carrier, the displayed family selects the element supplied by the choice axiom. If this same family commuted with every bijection, it would contradict the canonical two-point swap obstruction.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ClassicalChoiceNonnaturality.classical_choice_family_is_nonnatural`
- Dependency: [D5/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice](NoNaturalFiniteChoice.md)
