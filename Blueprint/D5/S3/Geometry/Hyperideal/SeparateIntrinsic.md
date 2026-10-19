# Intrinsic interiors separated by opposite supports

## Abstract

Opposite linear support signs separate the intrinsic interiors of two convex sets.

Let s and t be sets in the four-coordinate real space and let L be a real linear functional. If L is nonpositive on s, nonnegative on t, and is strictly negative somewhere in s, then the intrinsic interiors of s and t are disjoint.

**Theorem 1.1 (Opposite support signs exclude a common intrinsic-interior point).**

$$separateIntrinsic$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SeparateIntrinsic.separate_intrinsic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a hypothetical common interior point, linearity forces the support value to be zero. Intrinsic interior permits a positive extension away from any chosen point of s while staying in s. The strict negative witness then makes the extended support value positive, contradicting the nonpositive bound.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SeparateIntrinsic.separate_intrinsic`
