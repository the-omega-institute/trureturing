# Behavior Completion Extensivity

## Abstract

The realized behavior completion uniquely refines the current readout.

**Theorem 1.1 (Behavior completion refines the current readout).**

$$\forall X, B: \operatorname{Type},\ F: X \to X, q: X \to B,\ \exists! factor: \operatorname{ItineraryRange}\left(F, q\right) \to B,\ q = factor \circ \operatorname{rangeFactorization}\left(\operatorname{completeItinerary}\left(F, q\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/BehaviorCompletionExtensivity.behavior_completion_extensivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update states and let q be the current readout. The canonical complete itinerary records q after every iterate of F, while its realized range is the effective behavior-completion carrier.

There is a unique factor from that realized completion to the readout codomain whose composition with the canonical range factorization recovers q. Thus the completed interface refines q in the source's unique-factor sense.

The proof directly applies the exact observer-memory family theorem completion_extensivity; no completion or refinement primitive is redeclared.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/BehaviorCompletionExtensivity.behavior_completion_extensivity`
- Dependency: [D5/S3/ObserverMemory/Trajectories/CompletionExtensivity](CompletionExtensivity.md)
