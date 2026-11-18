# Transfer from local exclusion to global counting

## Abstract

A local exclusion by slightly relaxed distinct-prime thresholds gives a sharp global exponential upper bound.

**Theorem 1.1 (The sharp global exponent).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/CountingTransfer.count_from_local_exclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/CountingTransfer.count_from_local_exclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any decidable predicate on natural integers. Suppose that for every eta>0, all sufficiently large dyadic intervals (t/2,t] have each E-member above threshold(-eta,t) in distinct prime factors. Then, for every epsilon>0, the count of E-members up to x is eventually bounded by exp((C0+epsilon)*scale(x)). The existing saddle gives a tail bound with exponent C0+epsilon/4. A fixed initial segment and a logarithmic number of intervals introduce only a prefactor whose logarithm is negligible compared with scale(x); scale(2*x)/scale(x) tends to one. This theorem transfers a proved local exclusion. It does not supply that exclusion for Robin or real-power divisor inequalities.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/CountingTransfer.count_from_local_exclusion`
- Dependency: [D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting](Counting.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Selection](../OmegaTail/Selection.md)
