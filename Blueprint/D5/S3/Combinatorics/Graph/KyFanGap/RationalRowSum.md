# Rational constant weighted row sums

## Abstract

Rational constant weighted row sums.

**Theorem 1.1 (Rationality from symmetry).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum.rational_row_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum.rational_row_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be a symmetric rational matrix of any finite order R, p a real vector with coordinate sum one, and c a nonzero real number. If S p = c times the all-ones vector, then c is the real image of a rational number. A rational-linear retraction of the real field onto the rationals turns p/c into a rational solution w of S w = 1. Symmetry gives c times the coordinate sum of w equal to one, so c is the reciprocal of a nonzero rational number. No positivity or invertibility assumption is required.

**Theorem 1.2 (Nonsquare obstruction).**

Lean statement: `D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum.nonsquare_row_sum_ne`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum.nonsquare_row_sum_ne` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number k that is not a square, no symmetric rational matrix and real vector with coordinate sum one satisfy S p = (1/sqrt(k)) times the all-ones vector. The reciprocal square root is irrational, whereas the preceding theorem forces it to be rational. This includes symmetric matrices whose entries are minus one or one.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum.nonsquare_row_sum_ne`
- Truth anchor: `D5/S3/Combinatorics/Graph/KyFanGap/RationalRowSum.rational_row_sum`
