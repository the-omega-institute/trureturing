# Joint Rotation Factor Complexity

## Abstract

Joint Rotation Factor Complexity.

**Theorem 1.1 (A linear bound for simultaneous rotation words).**

Lean statement: `D5/S1/Words/Mechanical/JointRotationFactorComplexity.joint_rotation_factor_complexity`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Mechanical/JointRotationFactorComplexity.joint_rotation_factor_complexity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a finite nonempty set of positive integer scales, let alpha be irrational, and choose an integer offset b(a) at each scale. At phase x and time j, the coordinate at scale a is b(a) minus the indicator that the fractional part of a(x + j alpha) + alpha is at least one minus the fractional part of a alpha. For positive h, the set of length h vector words realized by x in [0,1) is finite and has cardinality at most (h + 1) times the sum of the scales in A. All coordinates use the same circle phase. Cutting the circle at one of the floor discontinuities allows the h + 1 floor samples at every scale to be counted together; equal cumulative counts determine equal vector words. The bound includes boundary phases.

## References

- Truth anchor: `D5/S1/Words/Mechanical/JointRotationFactorComplexity.joint_rotation_factor_complexity`
