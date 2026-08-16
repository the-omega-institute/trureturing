# Completion Criterion

## Abstract

The final observation quotient is its realized range and fills the formal-family space exactly under realizability.

**Theorem 1.1 (The kernel quotient completes exactly when every family is realized).**

$$(\exists! rangeEquiv: \operatorname{Quotient}(\ker observe) \equiv \operatorname{range}(observe), \forall x: X, rangeEquiv([x]) = observe(x)) \land ((\exists! limitEquiv: \operatorname{Quotient}(\ker observe) \equiv L, \forall x: X, limitEquiv([x]) = observe(x)) \Leftrightarrow \forall family: L, \exists x: X, observe(x) = family).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/CompletionCriterion.completion_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary observation map, final indistinguishability is equality of observations. The induced kernel quotient has a unique equivalence to the realized range that sends each class to its observed value.

The same quotient has a unique equivalence to the entire codomain that commutes with observation exactly when every formal family in that codomain is the observation of a global object.

Pinned Mathlib and Loogle supplied the exact reusable declarations Setoid.quotientKerEquivRange and Setoid.quotientKerEquivOfSurjective; both are imported and applied. Repository searches found only special finite-itinerary and controlled-behavior instances, while the LeanSearch query endpoint returned HTTP 404.

The statement retains both coupled clauses: identification with the realized range and the if-and-only-if criterion for filling the whole formal-family codomain. No finiteness, topology, or linearity assumption is added.

## References

- Truth anchor: `D5/S3/Observer/Separation/CompletionCriterion.completion_criterion`
