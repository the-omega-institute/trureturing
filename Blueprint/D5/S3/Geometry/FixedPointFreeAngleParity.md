# Fixed-point-free angle parity obstruction

## Abstract

A fixed-point-free involution forces an interval-bounded angle sum away from two pi.

Let a finite family carry a fixed-point-free involution. Its cardinality is even. If every angle lies strictly between pi/3 and pi/2, the sum cannot equal 2 pi: the cases of zero, two, or four angles are strictly below 2 pi, while six or more angles are strictly above it.

The statement is an abstract parity and interval obstruction. It supplies the numerical counting step used when a geometric pairing transports a fixed-point-free involution across the finite set of relevant edge occurrences. It does not assert the geometric hypotheses that produce that involution.

**Theorem 1.1 (Fixed-point-free angle sum obstruction).**

Lean statement: `D5/S3/Geometry/FixedPointFreeAngleParity.fixed_point_free_involution_interval_sum_ne_two_pi`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FixedPointFreeAngleParity.fixed_point_free_involution_interval_sum_ne_two_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite type with an involutive fixed-point-free self-map, any real-valued angle function whose values all lie in the open interval (pi/3, pi/2) has total sum different from 2 pi.

## References

- Truth anchor: `D5/S3/Geometry/FixedPointFreeAngleParity.fixed_point_free_involution_interval_sum_ne_two_pi`
- Dependency: [D5/S3/PrimeForms/Crossing/GlideCrossingParity](../PrimeForms/Crossing/GlideCrossingParity.md)
