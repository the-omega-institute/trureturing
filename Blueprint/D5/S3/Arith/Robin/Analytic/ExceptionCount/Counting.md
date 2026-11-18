# Distinct-prime tails and dyadic covers

## Abstract

Small fixed relaxations of the distinct-prime threshold preserve the sharp exponential counting rate, and dyadic intervals cover an arbitrary exception set.

**Theorem 1.1 (Stability under threshold relaxation).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting.relaxed_tail_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting.relaxed_tail_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive epsilon there is a positive eta for which tailCount(-eta,x) is eventually at most exp((C0+epsilon)*scale(x)). At the existing saddle s, the rate changes from C0 to C0+s*eta. Choosing eta=epsilon/(2*s) leaves half the exponent budget for the existing Rankin upper bound. This is a counting statement about distinct prime factors; it does not identify Robin exceptions.

**Theorem 1.2 (Exact finite cover by prime-factor tails).**

Lean statement: `D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting.dyadic_cover_count`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting.dyadic_cover_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary decidable predicate E, a natural cutoff N and an initial dyadic index J, suppose each E-member of (2^(j-1),2^j] above the initial segment has more distinct prime factors than threshold(lambda,2^j). Then the number of E-members in [1,N] is at most 2^J plus the sum of tailCount(lambda,2^j) over J<j<=clog(2,N). Each positive integer is assigned its natural upper logarithm. The finite-union bound preserves all small exceptions in the initial segment.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting.dyadic_cover_count`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/ExceptionCount/Counting.relaxed_tail_upper`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/Saddle](../OmegaTail/Saddle.md)
