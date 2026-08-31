# First-Claim Protocol Nonduplication

## Abstract

Finite T4-compliant atomic claim traces confine concurrent implementation to visibility windows, and their expected collision rate is monotone in trace delay.

**Theorem 1.1 (Atomic T4 traces prevent outside-window duplication).**

$$\begin{aligned}\forall O: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(O\right)],\\t: \operatorname{T4CompliantTrajectory}\left(O\right),\\\operatorname{ConcurrencyConfinedToVisibilityWindow}\left(\operatorname{toFiniteProtocol}\left(t\right)\right) \land\\{}\operatorname{Monotone}\left(\operatorname{collisionRate}\left(\operatorname{toFiniteProtocol}\left(t\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/OperationalTuition/FirstClaimProtocolNonduplication.t4_atomic_visibility_nonduplication_and_collision_rate_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite event list records implementation attempts, yield readouts, and reclaim readouts. Activity is a Boolean interval test, while exact atomic visibility begins at claim time plus the declared delay.

T4 compliance is structure evidence. A visible active holder forces another operator inactive and records the affected readout; reclaim attempts must follow the declared stall threshold and carry a matching trace.

Therefore simultaneous implementation can occur only before both claims become visible. Counting finite ordered claim pairs inside the delay window and normalizing by the fixed pair population makes collision rate monotone when trace delay increases.

## References

- Truth anchor: `D5/S3/ConceptDynamics/OperationalTuition/FirstClaimProtocolNonduplication.t4_atomic_visibility_nonduplication_and_collision_rate_monotone`
