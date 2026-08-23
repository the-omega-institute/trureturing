# Current Readout Recovery

## Abstract

Evaluation at time zero recovers the current readout from its complete itinerary.

**Theorem 1.1 (Recover the current readout).**

$$\forall X, B: \operatorname{Type},\ F: X \to X, q: X \to B,\ q = itineraryHead \circ \operatorname{completeItinerary}\left(F, q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/CurrentReadoutRecovery.recover_current_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update a state type X and let q read states into a type B. The complete itinerary of a state records q after every finite iterate of F, while itineraryHead evaluates such an itinerary at time zero.

The current readout q is exactly itineraryHead composed with the canonical complete-itinerary map. This is the theorem's sole public clause; it requires no finiteness or injectivity assumption.

The proof uses the imported family trajectory constructor directly. At coordinate zero, the zeroth iterate of F is the identity, so the two functions agree on every state.

Repository and pinned-library searches found the trajectory primitive and the iterate-zero computation, but no existing theorem for this raw recovery equality. The quotient-specific completion readout is a different map.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/CurrentReadoutRecovery.recover_current_readout`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
