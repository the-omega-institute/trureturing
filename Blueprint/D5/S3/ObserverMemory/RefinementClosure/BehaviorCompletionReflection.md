# Behavior Completion Reflection

## Abstract

Behavior completion is left adjoint to the inclusion of stable interfaces.

**Theorem 1.1 (Behavior completion has the stable-interface reflection property).**

$$\begin{gathered}\forall X, B, R,\\{}F: X \to X, q: X \to B, r: X \to R,\\{}(\operatorname{Surjective}(q) \land \operatorname{Surjective}(r) \land\\{}(\exists G: R \to R, r \circ F = G \circ r)) \Rightarrow\\{}(\exists! Phi: R \to \operatorname{ItineraryRange}(F, q), \operatorname{rangeFactorization}(\operatorname{completeItinerary}(F, q)) = Phi \circ r) \iff (\exists! \pi: R \to B, q = \pi \circ r).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionReflection.behavior_completion_reflection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update a state space X. Let q and r be interfaces onto their effective codomains, and suppose r carries an induced update commuting with F.

The behavior completion of q is the realized range of its full future itinerary. Refinement is stated by a unique factor map, matching the source interface order rather than hiding uniqueness in an auxiliary lemma.

If completion factors through r, its time-zero readout factor composes with that map to factor q through r. Surjectivity of r proves the composite factor is unique.

Conversely, the canonical behavior-completion minimality theorem sends any stable refinement of q uniquely onto the realized completion. Together the two implications are the reflection equivalence.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionReflection.behavior_completion_reflection`
- Dependency: [D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionMinimality](BehaviorCompletionMinimality.md)
- Dependency: [D5/S3/ObserverMemory/Trajectories/BehaviorCompletionExtensivity](../Trajectories/BehaviorCompletionExtensivity.md)
