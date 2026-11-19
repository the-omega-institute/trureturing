# Sharp Rankin upper bounds for distinct-prime tails

## Abstract

The continuous reserve controls the sharp Rankin upper exponent for distinct-prime tails.

**Theorem 1.1 (Upper bound for every sufficiently large real cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.sharp_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.sharp_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real epsilon and all sufficiently large real P, the count at exp(P) is at most exp((2*pi/sqrt(3) + epsilon)*Z(P)), where Z(P) = P/log(P)^(3/2). The count uses the strict second-order threshold P/log(P) + P/log(P)^2 and includes the case of a zero count.

Put c = pi/(2*sqrt(3)), s = c*log(P)^(1/2), and z = P^s. For each prime at most exp(P), split its logarithmic factor into the softplus weight at its absolute logarithmic distance from P and the term s*(log(P) - log(p)) supported on primes at most P. Summing these latter terms gives s*(pi(P)*log(P) - theta(P)). Combining with the Rankin prefactor gives s times the continuous reserve B0(P). The rounded reserve Bk(P) has the same leading limit.

The finite sum of nonnegative softplus weights is bounded by the summable total over primes. On the scale Z(P), the continuous reserve term tends to 2*c and the softplus sum tends to (pi^2/6)/c. The logarithmic correction from the p-series in the Rankin majorant is bounded for s at least two, so its ratio to Z(P) tends to zero. The two leading coefficients sum to 2*pi/sqrt(3).

This is the bound of Proposition 7.5 in the theory of the LCM-power Robin kappa threshold.

**Theorem 1.2 (Upper bound from a factorial reserve limit).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.factorial_sharp_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.factorial_sharp_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a natural number r at least two and a real threshold function T of P. Assume that the continuous reserve B(P) = P - theta(P) + (pi(P) - T(P))*log(P), divided by P/log(P)^r, tends to r! as P tends to infinity. For each positive real epsilon and all sufficiently large real P, the count of positive integers up to exp(P) with strictly more than T(P) distinct prime factors is strictly less than exp((pi*sqrt(2*r!/3) + epsilon)*Z(P)), where Z(P) = P/log(P)^((r+1)/2). The estimate includes a zero count.

Set c = pi/sqrt(6*r!), s = c*log(P)^((r-1)/2), and A = pi^2/6. The finite Rankin cancellation leaves s*B(P) and the softplus sum, whose ratios to Z(P) tend to r!*c and A/c, respectively. The p-series correction is bounded once s is at least two, and Z(P) tends to infinity. Since r!*c^2 = A, the two leading coefficients sum to pi*sqrt(2*r!/3).

This gives the analytic upper bound in Proposition 7.9 of the theory of the LCM-power Robin kappa threshold, with the reserve limit as a hypothesis.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.factorial_sharp_upper_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.sharp_upper_bound`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion](FarDeletion.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus](../../PriceRecord/MovingPrimeSoftplus.md)
