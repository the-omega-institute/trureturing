# Future-Itinerary Shift

## Abstract

Updating a state shifts its complete future itinerary by one coordinate.

**Theorem 1.1 (A state update shifts the complete future itinerary).**

$$\forall X, B,\ \forall update: X \to X,\ \forall readout: X \to B,\ \forall state\in X,\ \operatorname{completeItinerary}(update, readout, \operatorname{update}(state)) = \operatorname{tail}(\operatorname{completeItinerary}(update, readout, state)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/FutureItineraryShift.future_itinerary_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary state and readout types, let update advance the state and let readout expose one observation. The complete itinerary at a state is the stream whose n-th coordinate reads the n-fold update.

The complete itinerary starting after one update is exactly the stream tail of the itinerary starting at the current state.

The statement imports and exposes the repository's canonical completeItinerary and Mathlib's canonical Stream'.tail. The proof applies Function.iterate_succ_apply coordinatewise. Repository and pinned-Mathlib searches found no existing theorem with this exact family statement.

This formalizes theorem 41.9. It states the trajectory shift identity without adding finiteness, injectivity, or convergence assumptions.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/FutureItineraryShift.future_itinerary_shift`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
