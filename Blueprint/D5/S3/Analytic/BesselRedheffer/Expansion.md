# Explicit local comparison

## Abstract

A fourth-order obstruction to a normalized Bessel ratio bound.

**Theorem 1.1 (Failure from the energy upper bound).**

Lean statement: `D5/S3/Analytic/BesselRedheffer/Expansion.failure_of_energy_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/BesselRedheffer/Expansion.failure_of_energy_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let nu be at least 30 and let j be positive with j squared at most (6/5)(nu+1)(nu+7). There is a positive radius such that every positive x below that radius lies below j and the normalized Bessel ratio is strictly less than the proposed real-power lower bound with parameter j.

Put b=nu+1 and J=j squared. The common quadratic coefficient is 1/(4b(b+1)). The fourth-order coefficient of the ratio is R=1/(8b squared(b+1)(b+2)); that of the real power is L=1/(32b squared(b+1) squared)+1/(8b(b+1)J). The strict inequality R<L is equivalent to J<4b(b+1)(b+2)/(3b+2). The energy upper bound implies this inequality for b at least 31, since b squared-30b-16 is positive.

For nonnegative nu and absolute x at most one, the error after the quartic term in each normalized Bessel series has absolute value at most x to the sixth power. The denominator is at least one half when absolute x is at most one half. Multiplying the quartic approximation by the denominator and bounding the remaining terms gives ratio error at most 16 times x to the sixth power. The real binomial series has positive coefficients and bounds the real power below by its quadratic polynomial in x squared. A permitted radius is the minimum of j, one half, and (L-R)/32. This gives a strict violation at every positive x below that radius.

## References

- Truth anchor: `D5/S3/Analytic/BesselRedheffer/Expansion.failure_of_energy_bound`
- Dependency: [D5/S3/Analytic/BesselRedheffer/Series](Series.md)
