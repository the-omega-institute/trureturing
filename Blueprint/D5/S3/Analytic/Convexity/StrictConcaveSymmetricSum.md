# Symmetric sums and strict concavity

## Abstract

Strict concavity compares symmetric pairs with a common center.

**Theorem 1.1 (Symmetric sums of a strictly concave function).**

Lean statement: `D5/S3/Analytic/Convexity/StrictConcaveSymmetricSum.strictConcave_symmetric_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Convexity/StrictConcaveSymmetricSum.strictConcave_symmetric_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a strictly concave real function h on (0,infinity), and real r,s,t with 0<=s<t<r, one has h(r-t)+h(r+t)<h(r-s)+h(r+s). Both inner points are strict convex combinations of the outer pair. This comparison also gives strict decrease of equal-length increments.

## References

- Truth anchor: `D5/S3/Analytic/Convexity/StrictConcaveSymmetricSum.strictConcave_symmetric_sum`
