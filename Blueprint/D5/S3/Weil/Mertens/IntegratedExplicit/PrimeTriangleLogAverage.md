# Logarithmic averages of the ordinary-prime triangle

## Abstract

A lower bound on unit logarithmic windows of the ordinary-prime triangle characterizes RH.

**Theorem 1.1 (RH and a unit-window average of the centered prime triangle).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLogAverage.rh_iff_eventual_prime_triangle_log_average`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLogAverage.rh_iff_eventual_prime_triangle_log_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordinary-prime triangle is centered by its linear main term and the square-root term from prime squares. RH implies an eventual lower bound of minus one twelfth for the integral of the normalized expression over every unit interval in logarithmic coordinates. The reverse implication uses the dyadic recurrence for the smoothed Mangoldt ramp and telescopes its unit increments to an affine bound for the signed ordinary-prime primitive anchored at 5040.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleLogAverage.rh_iff_eventual_prime_triangle_log_average`
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/PrimeTriangleSquareLimit](PrimeTriangleSquareLimit.md)
- Dependency: [D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimePrimitiveCriterion](SignedPrimePrimitiveCriterion.md)
