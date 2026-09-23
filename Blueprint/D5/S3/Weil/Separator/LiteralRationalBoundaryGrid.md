# Literal Rational Pole-Boundary Grid

## Abstract

Exact rational cutoff and exponential enclosures feed a signed dyadic grid for the literal same-H pole-boundary computation.

**Definition 1.1 (Certified rational smooth-transition enclosure).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.cutoffCertified`

*Formalization.* `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.cutoffCertified` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For t at or below zero the result is exactly depth zero and [0,0]; for t at or above one it is exactly depth zero and [1,1]. For an interior rational t, finite search retains the first Taylor depth satisfying the rational predicate, both denominator and reciprocal checker calls, a signed enclosure of smoothTransition, and the requested dyadic width. The analytic proof fields are erased.

**Definition 1.2 (First certified signed exponential enclosure).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.boundaryExpCertified_v1`

*Formalization.* `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.boundaryExpCertified_v1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every rational exponent and natural precision, the definition returns the first positive Taylor depth accepted by the guard. Its actual rational Taylor interval encloses the real exponential, may have signed endpoints, and has width at most the requested dyadic tolerance.

**Theorem 1.3 (Signed four-corner interval multiplication).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.rationalIntervalMul_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.rationalIntervalMul_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The product interval takes the minimum and maximum of all four endpoint products. For ordered signed input intervals with amplitude caps, it remains ordered, inherits the product amplitude cap, and obeys the first-order width estimate A*width(b)+B*width(a). No positivity assumption is imposed on either input interval.

**Theorem 1.4 (Completed-square width across every sign branch).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.rationalIntervalSquare_width`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.rationalIntervalSquare_width` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring uses the lower endpoint squared on a nonnegative interval, the upper endpoint squared on a nonpositive interval, and lower endpoint zero when the interval crosses zero. All three branches satisfy the same twice-cap-times-width estimate.

**Definition 1.5 (Computed dyadic grid for the literal family).**

Lean statement: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.boundaryGrid`

*Formalization.* `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.boundaryGrid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For radius R, rational polynomials p and q, mesh depth k, and scalar depth s, this definition computes all cutoff and positive/negative exponential node enclosures and both families of checked cell expressions. The cell arithmetic keeps signed four-corner products; the final completed-square construction keeps the zero-crossing branch. The arrays are the concrete grid consumed by the semantic and rate certificates.

This module constructs rational ingredients for one literal same-H witness. It does not certify compact, prime, or Archimedean intervals, assert an off-line zero, extract a negative witness, or prove the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.boundaryExpCertified_v1`
- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.boundaryGrid`
- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.cutoffCertified`
- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.rationalIntervalMul_bounds`
- Truth anchor: `D5/S3/Weil/Separator/LiteralRationalBoundaryGrid.rationalIntervalSquare_width`
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](../../../S0/Certificates/BoxCover/RationalIntervalExpression.md)
