# Isometric p-adic linearization of the cubic Lucas update

## Abstract

A root-free coordinate conjugates multiplication by nine to the shifted cubic Lucas update on the entire small p-adic ball.

**Theorem 1.1 (Convergence throughout the small ball).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicPadicConjugacy.coordinate_summable`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicPadicConjugacy.coordinate_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorial valuation bound puts all coefficients of the rescaled series within a geometric norm bound. This proves summability for every point in the small p-adic ball at primes at least five.

**Theorem 1.2 (The full ball conjugacy and isometry).**

Lean statement: `D5/S3/Arith/Primes/GoldenCubicPadicConjugacy.linearizingIsometry_conj`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Primes/GoldenCubicPadicConjugacy.linearizingIsometry_conj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The evaluated coordinate is an isometric bijection of the closed ball of radius one over p. Its inverse follows from a strict contraction of the nonlinear remainder. Multiplication by nine becomes the cubic map y times (y+3) squared under this bijection. The identity is evaluated using summability and Cauchy products, and no square root of an input is selected.

## References

- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicPadicConjugacy.coordinate_summable`
- Truth anchor: `D5/S3/Arith/Primes/GoldenCubicPadicConjugacy.linearizingIsometry_conj`
- Dependency: [D5/S3/Arith/Primes/GoldenCubicFormalConjugacy](GoldenCubicFormalConjugacy.md)
