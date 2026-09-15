# Prime History Composition and Contextual Equivalence

## Abstract

The interval normal form is complete for contextual executability, not just an endpoint cache.

Composition is chronological: the first form runs first. For source intervals [l,u] and [l2,u2] and shifts d,d2, the composed source is [max(l,l2-d),min(u,u2-d)] and the shift is d+d2. Empty intersections produce the unique empty map. The interval is the constraint that one actual intermediate state must satisfy both histories.

**Theorem 1.1 (Actual concatenation descends to the computed composition).**

$$\forall a \in \mathbb{N},\; \forall v \in List\left(Bool\right),\; \forall w \in List\left(Bool\right),\; normal\left(a, List.append\left(v, w\right)\right) = compose\left(normal\left(a, v\right), normal\left(a, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/PrimeHistoryComposition.normal_append` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof first derives the exact intermediate-state evaluation law for the closed formula, then uses translated prefix extrema and extensional uniqueness. Nonempty intervals are distinguished by their endpoints and one output value. Merely adding net shifts would lose the necessary intersection condition.

**Theorem 1.2 (Contextual runs characterize the normal form).**

$$\forall a \in \mathbb{N},\; \forall v \in List\left(Bool\right),\; \forall w \in List\left(Bool\right),\; normal\left(a, v\right) = normal\left(a, w\right) \Leftrightarrow \left(\forall before \in List\left(Bool\right),\; \forall after \in List\left(Bool\right),\; \forall e \in Fin\left(a + 1\right),\; run\left(a, e, List.append\left(List.append\left(before, v\right), after\right)\right) = run\left(a, e, List.append\left(List.append\left(before, w\right), after\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/PrimeHistoryComposition.normal_eq_iff_contextual_run` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of normal forms is equivalent to equality of the exact partial runner in every prefix and suffix context and at every live state.

Contextual equality concerns total executability and final state. It is not equality of intermediate transcripts, elapsed duration, probabilities or costs. Group cancellation is unsafe at the guards: divide then multiply is an identity only on its proper source interval. No group action or Monster representation is inferred from the prime labels.

## References

- Truth anchor: `D5/S3/Factorization/Automata/PrimeHistoryComposition.normal_append`
- Truth anchor: `D5/S3/Factorization/Automata/PrimeHistoryComposition.normal_eq_iff_contextual_run`
- Dependency: [D5/S0/Automata/TypedPartialDFAOOverBase](../../../S0/Automata/TypedPartialDFAOOverBase.md)
- Dependency: [D5/S3/Factorization/Automata/BoundedPrimeHorizon](BoundedPrimeHorizon.md)
- Dependency: [D5/S3/Factorization/Automata/PrimeHistoryNormalForm](PrimeHistoryNormalForm.md)
