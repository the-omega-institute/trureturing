# Behavior Completion Functoriality

## Abstract

Behavior completion transports legal system translations functorially.

**Theorem 1.1 (Completion preserves translations and their composition).**

$$\begin{aligned}\forall X, Y, Z, B, R, S,\\F: X \to X, q: X \to B,\\G: Y \to Y, r: Y \to R,\\H: Z \to Z, s: Z \to S,\\h: X \to Y, eta: B \to R,\\k: Y \to Z, theta: R \to S,\\h \circ F = G \circ h,\\k \circ G = H \circ k,\\r \circ h = eta \circ q,\\s \circ k = theta \circ r \Rightarrow\\\operatorname{completionProjection}\left(G, r\right) \circ h = \operatorname{completionTransport}\left(h, eta\right) \circ \operatorname{completionProjection}\left(F, q\right) \land\\(\forall \phi: \operatorname{ItineraryRange}\left(F, q\right) \to \operatorname{ItineraryRange}\left(G, r\right), \operatorname{completionProjection}\left(G, r\right) \circ h = \phi \circ \operatorname{completionProjection}\left(F, q\right) \Rightarrow \phi = \operatorname{completionTransport}\left(h, eta\right)) \land\\\operatorname{completionTransport}\left(h, eta\right) \circ \operatorname{itineraryUpdate}\left(F, q\right) = \operatorname{itineraryUpdate}\left(G, r\right) \circ \operatorname{completionTransport}\left(h, eta\right) \land\\\operatorname{completionTransport}\left(\operatorname{id}\left(X\right), \operatorname{id}\left(B\right)\right) = \operatorname{id}\left(\operatorname{ItineraryRange}\left(F, q\right)\right) \land\\\operatorname{completionTransport}\left(k \circ h, theta \circ eta\right) = \operatorname{completionTransport}\left(k, theta\right) \circ \operatorname{completionTransport}\left(h, eta\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionFunctoriality.behavior_completion_is_functorial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A system translation consists of a state map commuting with the updates and a readout map commuting with the observations. It sends each realized source itinerary coordinatewise to a realized target itinerary.

The induced completion map makes the canonical projection square commute. Surjectivity of the source range factorization makes this map unique, while coordinate shifting proves that it semiconjugates the completed updates.

Coordinatewise transport by the identity readout map is the identity on completion, and transport by a composite readout map is the composite of the two induced completion maps.

The implementation reuses completeItinerary, ItineraryRange, itineraryUpdate, and the pinned range-factorization and semiconjugacy laws. Repository and library searches found no existing declaration packaging all five displayed clauses.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionFunctoriality.behavior_completion_is_functorial`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
