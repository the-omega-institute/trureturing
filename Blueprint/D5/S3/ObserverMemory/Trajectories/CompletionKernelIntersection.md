# Completion Kernel Intersection

## Abstract

The completion kernel is the intersection of all iterated readout-kernel pullbacks.

**Theorem 1.1 (The completion kernel is the intersection of iterated pullbacks).**

$$\forall X, B: \operatorname{Type},\ F: X \to X, q: X \to B,\ \left\{\operatorname{completeItinerary}\left(F, q\right)\left(\operatorname{fst}\left(p\right)\right) = \operatorname{completeItinerary}\left(F, q\right)\left(\operatorname{snd}\left(p\right)\right) \mid p \in X \times X\right\} = \operatorname{intersection}_{n \in \mathbb{N}} \operatorname{preimage}\left(\operatorname{Prod.map}(F^{n}, F^{n}), \left\{q\left(\operatorname{fst}\left(p\right)\right) = q\left(\operatorname{snd}\left(p\right)\right) \mid p \in X \times X\right\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/CompletionKernelIntersection.completion_kernel_eq_iterated_pullback_intersection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let F update a state type X and let q read states into B. The canonical completeItinerary is constructed from these two source primitives by recording q after every finite iterate of F.

The left side is displayed as the equality kernel of that canonical itinerary. The right side intersects, over every natural n, the preimage of the equality kernel of q under the paired map whose two coordinates are both the n-th iterate of F.

Equality of itineraries is equality at every coordinate. Applying congrArg at each coordinate proves one direction, and function extensionality proves the other.

Repository search found the canonical completeItinerary and the supporting finite-future intersection family, but no exact theorem packaging this completion-kernel identity. Pinned Mathlib supplies Setoid.ker, set preimages and intersections, Prod.map, and function iteration.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/CompletionKernelIntersection.completion_kernel_eq_iterated_pullback_intersection`
- Dependency: [D5/S3/Observer/Separation/FiniteFutureCongruence](../../Observer/Separation/FiniteFutureCongruence.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
