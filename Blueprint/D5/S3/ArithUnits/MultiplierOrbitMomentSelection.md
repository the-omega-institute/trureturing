# Multiplier-Orbit Moment Selection

## Abstract

Multiplicative invariance imposes a selection rule on arithmetic power moments.

**Theorem 1.1 (Nontrivial multiplier moments vanish).**

Lean statement: `D5/S3/ArithUnits/MultiplierOrbitMomentSelection.power_sum_zero_of_mul_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/MultiplierOrbitMomentSelection.power_sum_zero_of_mul_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a nonzero field element multiply a finite set onto itself. Reindexing its kth power sum by this permutation multiplies the same sum by the kth power of the multiplier. When that scalar is not one, cancellation in the field forces the sum to vanish. The result applies to invariant subsets, without requiring the whole field or a free action.

## References

- Truth anchor: `D5/S3/ArithUnits/MultiplierOrbitMomentSelection.power_sum_zero_of_mul_invariant`
