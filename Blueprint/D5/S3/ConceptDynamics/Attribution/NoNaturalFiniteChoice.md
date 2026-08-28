# No Natural Finite Choice

## Abstract

No selector on every nonempty finite carrier is invariant under all bijections.

**Theorem 1.1 (No natural finite choice).**

$$\neg \exists choice: \forall alpha: Type, f: \operatorname{Fintype}\left(alpha\right), h: \operatorname{Nonempty}\left(alpha\right), alpha, \forall alpha, beta: Type, fAlpha: \operatorname{Fintype}\left(alpha\right), fBeta: \operatorname{Fintype}\left(beta\right), hAlpha: \operatorname{Nonempty}\left(alpha\right), hBeta: \operatorname{Nonempty}\left(beta\right), e: \operatorname{Equiv}\left(alpha, beta\right), e\left(choice\left(alpha, fAlpha, hAlpha\right)\right) = choice\left(beta, fBeta, hBeta\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice.no_natural_finite_choice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A selector is supplied for every finite nonempty carrier, and its value is required to transport along every bijection between carriers. On the two-point carrier, swapping the two elements would have to fix the selected element.

The swap has no fixed point, so the transport law is impossible. The carrier type, finiteness and nonemptiness witnesses, and the bijection are all explicit in the statement.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice.no_natural_finite_choice`
