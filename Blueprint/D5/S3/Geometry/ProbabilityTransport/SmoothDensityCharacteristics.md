# Uniform closed-slab constants for the actual characteristics

## Abstract

Uniform closed-slab constants for the actual characteristics

**Theorem 1.1 (Uniform closed-slab constants for the actual characteristics).**

Lean statement: `D5/S3/Geometry/ProbabilityTransport/SmoothDensityCharacteristics.actual_smooth_slab_constants_including_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ProbabilityTransport/SmoothDensityCharacteristics.actual_smooth_slab_constants_including_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual chemical velocity on the closed smooth slab supplies uniform nonnegative constants B, L, K and C before any Euler mesh varies. They bound its speed, its spatial differential, its time increments, and the differential of the chosen C1 periodic terminal test. No transport or inverse-step assumption is used.

Spatial quotient periodicity reduces the norm bounds to a compact fundamental cell. For time increments, the joint relative differential is composed with the time inclusion, bounded on the compact slab cell, and transferred across spatial quotient fibres by equality of temporal functions. The closed-interval mean-value inequality supplies the time bound without differentiating a representative.

The constants theorem includes T equal to zero. In that branch both times equal zero, so K can be zero and only the smooth spatial slice is used. Every finite dimension, including zero, remains in scope.

For positive horizons, compact spatial bounds yield a global Lipschitz velocity and actual characteristic existence on the entire closed slab. Uniqueness yields quotient-fibre compatibility of the selected characteristicOperator. This result does not supply the independently requested C1 regularity in the initial point.

## References

- Truth anchor: `D5/S3/Geometry/ProbabilityTransport/SmoothDensityCharacteristics.actual_smooth_slab_constants_including_zero`
- Dependency: [D5/S3/Geometry/ProbabilityTransport/PeriodicDensityCalculus](PeriodicDensityCalculus.md)
