# Fixed-point-free angle support misses 2*pi

## Abstract

A fixed-point-free pairing leaves an even middle-angle support.

Let a finite family carry an involution without fixed points. Assume the involution preserves each angle and every angle is either zero or strictly between pi/3 and pi/2.

**Theorem 1.1 (Zero-or-middle angle sums miss 2*pi).**

Lean statement: `D5/S3/Geometry/Hyperideal/FixedPointFreeAngleParity.zero_or_middle_angle_sum_ne_two_pi`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FixedPointFreeAngleParity.zero_or_middle_angle_sum_ne_two_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restrict the involution to the subtype of nonzero angles. The restriction is still involutive and fixed-point-free, so this subtype has even cardinality. The strict middle-angle budget then places its sum strictly below or above 2*pi; the zero complement contributes nothing.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FixedPointFreeAngleParity.zero_or_middle_angle_sum_ne_two_pi`
- Dependency: [D5/S3/Geometry/Hyperideal/EvenAngleSumObstruction](EvenAngleSumObstruction.md)
- Dependency: [D5/S3/PrimeForms/Crossing/GlideCrossingParity](../../PrimeForms/Crossing/GlideCrossingParity.md)
