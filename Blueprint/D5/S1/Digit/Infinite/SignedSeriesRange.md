# The Range of the Signed Golden Series

## Abstract

The Range of the Signed Golden Series.

**Theorem 1.1 (The interval and its endpoint fibres).**

Lean statement: `D5/S1/Digit/Infinite/SignedSeriesRange.signed_series_range`

*Proof.* Machine-checked in Lean as `D5/S1/Digit/Infinite/SignedSeriesRange.signed_series_range` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let alpha be the reciprocal of the golden ratio. For infinite Boolean digits with no adjacent ones, indexed from low to high, the sum of the digits with coefficients minus alpha squared, alpha cubed, minus alpha to the fourth, and so on has range exactly the closed interval from minus alpha to alpha squared. The lower endpoint is attained only by the alternating stream starting with one, and the upper endpoint only by the alternating stream starting with zero. Every real number outside this interval has empty fibre. Termwise comparison gives the bounds and strictness away from the alternating streams. Repeated inverse branches construct legal digits for every point in the interval, with a remainder tending to zero.

## References

- Truth anchor: `D5/S1/Digit/Infinite/SignedSeriesRange.signed_series_range`
- Dependency: [D5/S1/Digit/Infinite/SuccessorContinuity](SuccessorContinuity.md)
