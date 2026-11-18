# Geometric tails of the moving weight

## Abstract

Integer majorants for the tails of a moving localized prime weight.

**Theorem 1.1 (Finite inverse-power tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.finite_power_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.finite_power_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real s>1, every positive natural cutoff N, and every finite set S of natural numbers strictly larger than N, the sum of n^(-s) over S is at most N^(1-s)/(s-1). The bound compares the finite sum with the integral over all real t>N.

**Theorem 1.2 (Small-endpoint geometric tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.small_weight_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.small_weight_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>=2 and s>=0, summing log(1+exp(-s*abs(log(n/P)))) over any finite set of positive natural numbers n<=P/2 gives at most P*(1/2)^s. This bound also applies to any selected primes in that range.

**Theorem 1.3 (Large-endpoint geometric tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.large_weight_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.large_weight_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For P>=2 and s>=2, the same localized weight summed over any finite set of natural numbers strictly greater than 2P is at most 2P*(2/3)^s. The real-to-natural cutoff is retained explicitly before the inverse-power tail estimate.

**Theorem 1.4 (Decay at the square-root logarithmic saddle).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.geometric_sqrt_decay`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.geometric_sqrt_decay` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every fixed c>0 and 0<q<1, t*sqrt(t)*q^(c*sqrt(t)) tends to zero as t tends to positive infinity. Thus each geometric tail vanishes on the normalized second-threshold scale at its explicit saddle. A matching lower counting bound is not established here.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.finite_power_tail`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.geometric_sqrt_decay`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.large_weight_tail`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSecond/Tail.small_weight_tail`
