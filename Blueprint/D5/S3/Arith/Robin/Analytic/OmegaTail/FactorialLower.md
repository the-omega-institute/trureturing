# Fixed-order factorial tails

## Abstract

A lower transfer for the strict distinct-prime tail at any fixed factorial order.

**Theorem 1.1 (Sharp lower bound for the literal factorial tail).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialLower.factorial_tail_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialLower.factorial_tail_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix an integer r at least two. The prime base at centre P must eventually lie below P, contain all primes in (3P/4, P], and have cardinality strictly above P times the sum of j! divided by log(P) to the power j+1 for j from 0 to r-1. Its log sum is at most P minus a reserve whose ratio to P divided by log(P) to the power r tends to r!.

Set A = pi squared divided by 6, c = pi divided by the square root of 6r!, and K = 2A/c. The logistic grid gives an exchange with normalized cost strictly below A(1+eta)^2, where eta = epsilon/(8K). The signed moving-box limits give the two capacities, and the donor endpoints divided by P tend to one. The actual family provided by the log-power exchange fits the reserve. Its entropy loses at most epsilon times c divided by 8 before multiplication by the box scale, in addition to the same grid approximation tolerance.

Every output is a positive natural number below exp(P) and has exactly the base cardinality in distinct prime factors. Consequently it belongs to the finite interval from 1 through floor(exp(P)) filtered by the strict factorial threshold. The literal count is eventually positive, and its logarithm is at least (K minus epsilon) times P divided by log(P) to the power (r+1)/2.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/FactorialLower.factorial_tail_lower`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/LogPowerExchange](LogPowerExchange.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/LogisticGrid](LogisticGrid.md)
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/MovingBoxCapacity](MovingBoxCapacity.md)
