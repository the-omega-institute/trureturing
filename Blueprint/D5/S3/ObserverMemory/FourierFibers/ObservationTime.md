# Observation Time as a Fiber Boundary

## Abstract

The canonical separation time is the exact boundary at which an eventually separated pair leaves every finite observation fiber.

**Theorem 1.1 (Finite fiber membership ends at the first visible time).**

$$(\exists t, \operatorname{observedAt}(t, left) \neq \operatorname{observedAt}(t, right)) \Rightarrow ((left, right) \in \operatorname{finiteFutureRelation}(horizon) \Leftrightarrow horizon < \operatorname{separationTime}(left, right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FourierFibers/ObservationTime.finite_future_membership_iff_before_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a pair that is separated at some finite dynamical readout, membership in the canonical finite-future relation holds exactly before the repository separationTime.

The module reuses observedAt, finiteFutureRelation, infiniteFutureRelation, and separationTime. It introduces no competing time or observation-window API and makes no identification with physical time.

## References

- Truth anchor: `D5/S3/ObserverMemory/FourierFibers/ObservationTime.finite_future_membership_iff_before_separation`
- Dependency: [D5/S3/Observer/Separation/FiniteFutureCongruence](../../Observer/Separation/FiniteFutureCongruence.md)
