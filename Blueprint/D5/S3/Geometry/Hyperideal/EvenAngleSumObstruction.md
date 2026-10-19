# Even middle-angle sums cannot close at 2*pi

## Abstract

An even number of middle angles cannot sum to two pi.

Consider a finite family of real angles with even cardinality. If every angle lies strictly between pi/3 and pi/2, then the total cannot equal 2*pi.

**Theorem 1.1 (Even middle angles cannot close).**

Lean statement: `D5/S3/Geometry/Hyperideal/EvenAngleSumObstruction.even_middle_angle_sum_ne_two_pi`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/EvenAngleSumObstruction.even_middle_angle_sum_ne_two_pi` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an empty family the sum is zero. For a nonempty family, write its even cardinality as twice k. If k is at most two, the strict upper bound pi/2 makes the total strictly less than 2*pi. If k is at least three, the strict lower bound pi/3 makes the total strictly greater than 2*pi.

This is the numerical angle-budget component of the low-face transport obstruction. It assumes the even-cardinality fact supplied by a separate face-pairing argument and does not itself construct the pairing, classify the six-length shape family, or prove a global geometric realization.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/EvenAngleSumObstruction.even_middle_angle_sum_ne_two_pi`
