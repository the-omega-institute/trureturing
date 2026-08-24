# Completion Extensivity

## Abstract

Every readout factors uniquely through its realized complete itinerary.

**Theorem 1.1 (A readout is refined by its complete itinerary).**

$$\forall X, B: \operatorname{Type},\ F: X \to X, q: X \to B,\ \exists! factor: \operatorname{ItineraryRange}\left(F, q\right) \to B,\ q = factor \circ \operatorname{rangeFactorization}\left(\operatorname{completeItinerary}\left(F, q\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/CompletionExtensivity.completion_extensivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update a state type X and let q read states into B. The complete itinerary records every future q-value, and its realized range is the effective completion carrier.

There is a unique map from that realized itinerary range to B whose composition with the canonical range factorization recovers q. This directly expresses the refinement clause on effective images, including the source theorem's uniqueness.

The factor evaluates an itinerary at time zero. Current readout recovery proves existence, while surjectivity of the canonical range factorization lets composition cancellation prove uniqueness.

Repository search found the canonical completeItinerary, ItineraryRange, and current-readout recovery declarations. Pinned Mathlib supplies rangeFactorization, its surjectivity, and right-composition cancellation; no exact packaged theorem was found.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/CompletionExtensivity.completion_extensivity`
- Dependency: [D5/S3/ObserverMemory/Trajectories/CurrentReadoutRecovery](CurrentReadoutRecovery.md)
