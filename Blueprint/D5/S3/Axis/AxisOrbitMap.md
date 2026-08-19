# Axis Orbit Map

## Abstract

The two trace recurrences are exactly one orbit of a four-dimensional polynomial map.

The weight recurrence and the partial-sum recurrence were proved separately. Read together they are not two laws but one: the state holding the two latest partial sums and the two latest weights advances by a single polynomial map, and each recurrence supplies one of its coordinates while the remaining two are shifts.

Stating this is what rules out a third law hiding in the pair. Without the orbit form the two recurrences merely coexist; with it, every depth is an iterate of one map from one base state.

**Theorem 1.1 (The trace recurrences are one orbit).**

$$\forall K\in \mathbb{N},\ F(S_{K}) = S_{K+1}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisOrbitMap.trace_recurrences_are_one_orbit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed conjunct is the single step; the package also carries that the state at every depth is the corresponding iterate.

## References

- Truth anchor: `D5/S3/Axis/AxisOrbitMap.trace_recurrences_are_one_orbit`
- Dependency: [D5/S3/Axis/AxisPartialSum](AxisPartialSum.md)
