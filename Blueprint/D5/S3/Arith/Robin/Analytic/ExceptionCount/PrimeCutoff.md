# Prime cutoff and its capacity

## Abstract

An explicit cutoff with sufficient prime capacity and a strict logarithmic gap.

**Definition 1.1 (Prime cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff`

*Formalization.* `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For t the cutoff is exp(t-1/(2t)), strictly below exp(t) for positive t.

**Theorem 1.2 (Divergence of the cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff_top`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cutoff tends to positive infinity as t tends to positive infinity.

**Theorem 1.3 (Prime capacity at the cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.enough_primes`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.enough_primes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Eventually the real prime count below exp(t-1/(2t)) is at least exp(t)/t. The second prime-counting coefficient supplies a positive residual limit of one half after normalization.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.cutoff_top`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/PrimeCutoff.enough_primes`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](../../PriceRecord/QuantitativePrimeAbel.md)
