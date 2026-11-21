# Negative tail mass of a monotone count

## Abstract

Upper bounds from a centered signed primitive

**Theorem 1.1 (Bounds on the actual tail and its weighted negative mass).**

Lean statement: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimitiveUpper.signedPrimitiveUpper`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimitiveUpper.signedPrimitiveUpper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a real counting function, nondecreasing above X₀ ≥ 1. Let q(x) be the integral from x to infinity of (A(t)−t)/t², and assume this kernel is integrable above X₀. For κ ≥ 0 assume the absolute value of the signed integral of q(x)/√x on every real interval [a,b] with X₀ ≤ a ≤ b, centered by adding κ log(b/a), is at most C.

For every real x ≥ 3X₀/2, q(x) ≥ −κ/√x − (2C+1/6)x^(−1/3). For all real a,b with 3X₀/2 ≤ a ≤ b, the integral of max(−q(x),0)/√x on [a,b] is at most κ log(b/a) + (12C+1)(b^(1/6)−a^(1/6)).

In reciprocal coordinates u=1/x the sum q(1/u)+log u is concave, since its secant slopes are averages of the nonincreasing function A(1/u). Apply a midpoint estimate on the interval centered at u with radius u^(7/6)/2. The signed primitive controls the interval integral and the midpoint estimate bounds the concavity correction from log u. The resulting pointwise estimate integrates to the stated bound.

## References

- Truth anchor: `D5/S3/Weil/Mertens/IntegratedExplicit/SignedPrimitiveUpper.signedPrimitiveUpper`
