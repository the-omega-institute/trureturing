# Behavior Completion Functoriality

## Abstract

Behavior completion transports legal system translations functorially.

**Theorem 1.1 (Completion preserves translations and their composition).**

$$\begin{aligned}\forall X: \operatorname{Type}, Y: \operatorname{Type}, Z: \operatorname{Type}, B: \operatorname{Type}, R: \operatorname{Type}, S: \operatorname{Type},\\F: X \to X, q: X \to B,\\G: Y \to Y, r: Y \to R,\\H: Z \to Z, s: Z \to S,\\h: X \to Y, eta: B \to R,\\k: Y \to Z, theta: R \to S,\\hstep: \operatorname{Semiconj}\left(h, F, G\right),\\kstep: \operatorname{Semiconj}\left(k, G, H\right),\\hreadout: {\forall x: X, r\left(h\left(x\right)\right) = eta\left(q\left(x\right)\right)},\\kreadout: {\forall y: Y, s\left(k\left(y\right)\right) = theta\left(r\left(y\right)\right)} \Rightarrow\\\operatorname{rangeFactorization}\left(\operatorname{completeItinerary}\left(G, r\right)\right) \circ h = \operatorname{completionTransport}\left(F, q, G, r, h, eta, hstep, hreadout\right) \circ \operatorname{rangeFactorization}\left(\operatorname{completeItinerary}\left(F, q\right)\right) \land\\(\forall \phi: \operatorname{ItineraryRange}\left(F, q\right) \to \operatorname{ItineraryRange}\left(G, r\right), \operatorname{rangeFactorization}\left(\operatorname{completeItinerary}\left(G, r\right)\right) \circ h = \phi \circ \operatorname{rangeFactorization}\left(\operatorname{completeItinerary}\left(F, q\right)\right) \Rightarrow \phi = \operatorname{completionTransport}\left(F, q, G, r, h, eta, hstep, hreadout\right)) \land\\\operatorname{Semiconj}\left(\operatorname{completionTransport}\left(F, q, G, r, h, eta, hstep, hreadout\right), \operatorname{itineraryUpdate}\left(F, q\right), \operatorname{itineraryUpdate}\left(G, r\right)\right) \land\\\operatorname{completionTransport}\left(F, q, F, q, id, id, idLeft, {\Lambda x: X, rfl}\right) = id \land\\\operatorname{completionTransport}\left(F, q, H, s, k \circ h, theta \circ eta, \operatorname{trans}\left(hstep, kstep\right), {\Lambda x: X, \operatorname{trans}\left(kreadout\left(h\left(x\right)\right), \operatorname{congrArg}\left(theta, hreadout\left(x\right)\right)\right)}\right) = \operatorname{completionTransport}\left(G, r, H, s, k, theta, kstep, kreadout\right) \circ \operatorname{completionTransport}\left(F, q, G, r, h, eta, hstep, hreadout\right).\end{aligned}$$

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
