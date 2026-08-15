# Uniform Escape Probability Bounds

## Abstract

Uniform escape probability lies in the closed unit interval for all finite address and output types.

**Theorem 1.1 (Uniform escape probability is between zero and one).**

$$\forall A, [\operatorname{Fintype} A], \forall Y, [\operatorname{Fintype} Y], \forall f: Y \to Y, 0 \leq \operatorname{escapeProbability}\left(A, f\right) \land \operatorname{escapeProbability}\left(A, f\right) \leq 1.$$

*Proof.* Machine-checked in Lean as `D5/S0/Asymptotics/EscapeProbability/ProbabilityBounds.escape_probability_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The escaped listings form a subtype of the finite space of all listings. Their cardinality is therefore at most the total cardinality, while both cardinalities are nonnegative. Dividing these cardinalities in the frozen definition gives the two bounds, including when the listing space is empty.

Pinned Mathlib supplies Finite.card_subtype_le and the nonnegative division lemmas used to compare the uniform escape ratio with zero and one.

## References

- Truth anchor: `D5/S0/Asymptotics/EscapeProbability/ProbabilityBounds.escape_probability_bounds`
- Dependency: [D5/S0/Asymptotics/FixedPointFreeEscapeProbability](../FixedPointFreeEscapeProbability.md)
