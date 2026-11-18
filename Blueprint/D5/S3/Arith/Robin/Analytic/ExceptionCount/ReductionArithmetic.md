# Arithmetic reduction to prime prefixes

## Abstract

Finite arithmetic bounds for exception counting.

**Theorem 1.1 (Mertens product upper bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic.robin_product_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic.robin_product_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The divisor ratio is at most the canonical finite Mertens product when the cutoff contains at least as many primes as the support of n. This identifies the arithmetic bound with the analytic product used for the strict logarithmic gap.

**Theorem 1.2 (Uniform kappa product bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic.kappa_product_tail_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic.kappa_product_tail_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive delta there is a nonnegative constant C such that, for kappa at least 1+delta, P at least 2, n nonzero, and omega(n) at most pi(P), the bound zeta(kappa) sigma^[kappa](n) / n^kappa <= (M(P) * exp(C P^(-delta/2)))^kappa holds uniformly in kappa, P, and n, where M(P) is the finite Mertens product. The proof separates the omitted Euler factors and uses the uniform logarithmic tail estimate.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic.kappa_product_tail_upper`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionArithmetic.robin_product_upper`
- Dependency: [D5/S3/Arith/ExponentExchange/IntegerSwap](../../../ExponentExchange/IntegerSwap.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal](ReductionLocal.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/ZetaTail](ZetaTail.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/LcmPowerEndpointExpansion](../LcmPowerEndpointExpansion.md)
- Dependency: [D5/S3/Arith/Robin/FibonacciPrimeSupport](../../FibonacciPrimeSupport.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/PrimePowerEnvelope](../../PriceRecord/PrimePowerEnvelope.md)
