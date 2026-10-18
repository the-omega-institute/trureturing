# Affine span of a four-point sum-one family

## Abstract

Four affine-independent points in a common sum-one hyperplane span that hyperplane.

Work in the four-coordinate real space and let sumOne be the affine hyperplane whose coordinates sum to one. If four points are affine independent and each lies in sumOne, their affine span is all of sumOne.

**Theorem 1.1 (Four independent points span the sum-one hyperplane).**

$$spanSumOne$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/SpanSumOne.span_sumOne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Affine independence gives a linear basis for the four-dimensional coordinate space. Every point of sumOne has a unique expansion in that basis, and its coefficients sum to one because each basis point does.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/SpanSumOne.span_sumOne`
