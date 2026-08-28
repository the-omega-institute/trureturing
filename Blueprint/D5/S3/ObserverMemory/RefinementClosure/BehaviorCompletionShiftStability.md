# Behavior Completion Shift Stability

## Abstract

The complete behavior interface carries the restricted left-shift dynamics.

**Theorem 1.1 (Completion intertwines the update and itinerary shift).**

$$\begin{aligned}\forall X: \operatorname{Type}, B: \operatorname{Type},\\F: X \to X, q: X \to B,\\(\forall x: X, \operatorname{completeItinerary}\left(F, q\right)(F(x)) = \operatorname{tail}\left(\operatorname{completeItinerary}\left(F, q\right)(x)\right)) \land\\\operatorname{rangeFactorization}\left(\operatorname{completeItinerary}\left(F, q\right)\right) \circ F = \operatorname{itineraryUpdate}\left(F, q\right) \circ \operatorname{rangeFactorization}\left(\operatorname{completeItinerary}\left(F, q\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionShiftStability.behavior_completion_shift_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete itinerary and its realized range are the existing family primitives, constructed from the state update and readout.

After one state update, every complete future word is the tail of the previous word. The imported future-itinerary theorem supplies this first public equality directly.

The same tail operation restricts to realized words because the shifted word is realized by the updated state. The second public equality states the resulting induced dynamics on the exact completion carrier.

## References

- Truth anchor: `D5/S3/ObserverMemory/RefinementClosure/BehaviorCompletionShiftStability.behavior_completion_shift_stability`
- Dependency: [D5/S3/ObserverMemory/Trajectories/FutureItineraryShift](../Trajectories/FutureItineraryShift.md)
