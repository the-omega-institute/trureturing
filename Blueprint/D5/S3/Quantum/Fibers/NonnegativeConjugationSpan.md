# Nonnegative Waits and Commutator Jets

## Abstract

Commutator jets lie in the span of actual nonnegative-time matrix conjugations.

**Theorem 1.1 (Every commutator jet belongs to the observation span).**

$$\forall n:Type,[\operatorname{Fintype}(n)][\operatorname{DecidableEq}(n)],\forall A,X:\operatorname{RealMatrix}(n),\forall k\in \mathbb{N},t\in \mathbb{R},0\leq t\Rightarrow \operatorname{conjugate}(A,\operatorname{iterate}(\operatorname{commutator}(A),k,X),t)\in \operatorname{observationSpan}(A,X)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fibers/NonnegativeConjugationSpan.commutator_jets_in_nonnegative_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite real matrices A and X, conjugate X by the exponential of t A, with inverse exponential on the left. The observation span uses only nonnegative real times. Its finite dimension makes it closed.

The derivative is the same conjugation of the commutator X A minus A X. Difference quotients within the nonnegative half-line remain in the observation span. Closure puts their derivatives there, and induction gives every iterated commutator at every nonnegative time, including time zero.

This analytic implication allows exact algebraic spanning information about commutator jets to imply a statement about actual waiting effects. It does not add a derivative measurement to the menu, and it does not by itself certify the rank of a particular five-mode family.

## References

- Truth anchor: `D5/S3/Quantum/Fibers/NonnegativeConjugationSpan.commutator_jets_in_nonnegative_span`
