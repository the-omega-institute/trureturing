# Behavior Completion Translation

## Abstract

A legal system translation induces one and only one map between behavior completions.

**Theorem 1.1 (The induced completion map exists uniquely).**

$$\begin{aligned}\forall X: \operatorname{Type}, Y: \operatorname{Type}, B: \operatorname{Type}, R: \operatorname{Type},\\F: X \to X, q: X \to B,\\G: Y \to Y, r: Y \to R,\\h: X \to Y, eta: B \to R,\\h \circ F = G \circ h,\\r \circ h = eta \circ q \Rightarrow\\\exists ! \operatorname{C}\left(h\right): \operatorname{ItineraryRange}\left(F, q\right) \to \operatorname{ItineraryRange}\left(G, r\right),\\\operatorname{completionProjection}\left(G, r\right) \circ h = \operatorname{C}\left(h\right) \circ \operatorname{completionProjection}\left(F, q\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionTranslation.behavior_completion_translation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source and target completion carriers are the realized ranges of their full future readout itineraries.

A state map commuting with the updates and a compatible readout map transport each realized source itinerary coordinatewise to the target completion.

The resulting map makes the canonical completion square commute. Surjectivity of the source range factorization makes this map unique.

The proof imports the canonical completion transport and projects the commuting and uniqueness clauses of the frozen functoriality law.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionTranslation.behavior_completion_translation`
- Dependency: [D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionFunctoriality](BehaviorCompletionFunctoriality.md)
