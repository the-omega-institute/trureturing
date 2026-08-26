# Same-Fiber Path Orbit Criterion

## Abstract

Inside one visible solenoid fiber, path components are integer real-flow orbits.

**Proposition 1.1 (Joined points in one fiber differ by integer flow time).**

$$\forall x, y: UniversalSolenoid, \operatorname{projection}\left(x\right) = \operatorname{projection}\left(y\right) \Rightarrow (\operatorname{Joined}\left(x, y\right) \Leftrightarrow \exists n: \mathbb{Z}, y = \operatorname{realFlow}\left(n\right) + x).$$

*Proof.* Machine-checked in Lean as `D5/S1/Solenoid/Connectivity/SameFiberPathOrbitCriterion.same_fiber_path_orbit_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The carrier is the repository's universal solenoid, with its canonical visible projection, real flow, and Mathlib path-joining relation.

The imported path-orbit classification first gives an arbitrary real flow time. Equality of visible projections makes that time zero in the period-one additive circle.

The pinned additive-circle kernel theorem identifies such times with integers. Conversely, every integer-time translation is already a real-flow translation and therefore supplies a joining path.

## References

- Truth anchor: `D5/S1/Solenoid/Connectivity/SameFiberPathOrbitCriterion.same_fiber_path_orbit_criterion`
- Dependency: [D5/S1/Solenoid/PathOrbitClassification](../PathOrbitClassification.md)
