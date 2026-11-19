# Strict Mertens product gap

## Abstract

A strict initial-prime Euler product gap absorbs a power-decaying omitted Euler tail.

**Definition 1.1 (Initial-prime inverse product).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap.product`

*Formalization.* `D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap.product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite inverse Euler product contains exactly the primes at most the real cutoff, including equality at a prime cutoff.

**Theorem 1.2 (Upper-half interval gap).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap.upper_half_product_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap.upper_half_product_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive a and every fixed real C, the product at P=exp(t-1/(2t)), multiplied by exp(C P^(-a)), is eventually at most exp(gamma)(t-1/(4t)). The strengthened Mertens error is o(1/t^2) at this cutoff. The extra logarithmic Euler tail is also o(1/t^2), so the exponential perturbation consumes less than half the prescribed gap.

With t=log(log(x)), this perturbed initial-prime product is eventually strictly less than exp(gamma) log(log(x/2)). The logarithmic tangent inequality bounds the shift from x to x/2 by log(2)/(log(x)-log(2)), which is o(1/log(log(x))). This strict estimate is uniform over every integer in the upper half interval after monotonicity of log(log(n)).

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap.product`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/MertensGap.upper_half_product_gap`
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/Mertens](Mertens.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff](PrimeCutoff.md)
