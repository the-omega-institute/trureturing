# Seven-phase source coordinates

## Abstract

Seven-phase source coordinates.

**Definition 1.1 (Subcritical observation radius).**

Lean statement: `D5/S1/Digit/Infinite/SevenCycleCollisionData.budget`

*Formalization.* `D5/S1/Digit/Infinite/SevenCycleCollisionData.budget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The radius is lambda minus g^7*(g-1/5)/(4*(1+g^7)), where g is the original three-bit contraction. The source streams repeat the windows 3,3,5,5,3,2,2 and 0,3,5,5,3,2,2. Their guards are 0,0,0,1,1,0,0. The scalar phase function uses the original branch maps for the common six-window suffix.

## References

- Truth anchor: `D5/S1/Digit/Infinite/SevenCycleCollisionData.budget`
- Dependency: [D5/S1/Digit/Infinite/ClosedObservationGraphRealization](ClosedObservationGraphRealization.md)
