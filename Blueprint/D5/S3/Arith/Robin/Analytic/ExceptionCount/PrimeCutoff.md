# Prime cutoff and its capacity

## Abstract

An explicit cutoff with sufficient prime capacity and a strict logarithmic gap.

**Theorem 1.1 (Second prime-counting coefficient).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.second_order_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.second_order_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized second-order prime-counting error log(x)*(log(x)*primeCount(x)/x-1) tends to one. The same result supplies the uniform central density estimate used for prime exchanges.

**Definition 1.2 (Prime cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff`

*Formalization.* `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For t the cutoff is exp(t-1/(2t)), strictly below exp(t) for positive t.

**Theorem 1.3 (Divergence of the cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff_top`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff tends to positive infinity as t tends to positive infinity.

**Theorem 1.4 (Prime capacity at the cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.enough_primes`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.enough_primes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eventually the real prime count below exp(t-1/(2t)) is at least exp(t)/t. The second prime-counting coefficient supplies a positive residual limit of one half after normalization.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff_top`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.enough_primes`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.second_order_count`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](../../PriceRecord/QuantitativePrimeAbel.md)
