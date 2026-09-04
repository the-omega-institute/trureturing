# Free Permutation Observer Distance

## Abstract

Free update orbits have exact integer distance, while both off-orbit sectors are infinitely far.

**Theorem 1.1 (Free orbits have exact observer distance).**

$$\forall I, Fiber, tau \in \operatorname{EquivPerm}(I), fiber \in \operatorname{Map}(I, Fiber),\ \operatorname{Free}(tau) \land \operatorname{Invariant}(fiber, tau) \Rightarrow \ (\forall x \in I, n \in \mathbb{Z}, \operatorname{observerDistance}(tau, x, \operatorname{act}(tau^{n}, x)) = \left|n\right|) \land\ (\forall x, y \in I, fiber(x) = fiber(y) \land \neg y \in \operatorname{Orb}(tau, x) \Rightarrow \operatorname{observerDistance}(tau, x, y) = \infty) \land\ (\forall x, y \in I, fiber(x) \neq fiber(y) \Rightarrow \operatorname{observerDistance}(tau, x, y) = \infty).$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/FreePermutationObserverDistance.free_permutation_observer_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integer-power action is required to be free. This premise is necessary: on a periodic orbit a nonzero period returns to the starting point, so the distance is zero rather than the absolute value of that period.

For the missing lower bound, the proof assigns each point of the selected orbit its unique integer coordinate and clips its distance from zero at the requested radius. This readout is bounded, changes by at most one under one update, and attains the full integer displacement.

The same-fiber off-orbit clause uses the frozen characterization of infinite distance by distinct cyclic update orbits. The distinct-fiber clause applies the frozen invariant-leaf separator directly.

## References

- Truth anchor: `D5/S3/ContinuousObservables/FreePermutationObserverDistance.free_permutation_observer_distance`
- Dependency: [D5/S3/ContinuousObservables/PermutationOrbitHorizon](PermutationOrbitHorizon.md)
