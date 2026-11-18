# Sharp Rankin upper bound at the second threshold

## Abstract

The second distinct-prime threshold admits an upper exponent of order P divided by log(P) to the power 3/2.

**Theorem 1.1 (Upper bound for every sufficiently large real cutoff).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.sharp_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.sharp_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive real epsilon and all sufficiently large real P, the count at exp(P) is at most exp((2*pi/sqrt(3) + epsilon)*Z(P)), where Z(P) = P/log(P)^(3/2). The count uses the strict second-order threshold P/log(P) + P/log(P)^2 and includes the case of a zero count.

Put c = pi/(2*sqrt(3)), s = c*log(P)^(1/2), and z = P^s. For each prime at most exp(P), split its logarithmic factor into the softplus weight at its absolute logarithmic distance from P and the term s*(log(P) - log(p)) supported on primes at most P. Summing these latter terms gives s*(pi(P)*log(P) - theta(P)). Combining with the Rankin prefactor gives s times the continuous reserve B0(P). The rounded reserve Bk(P) has the same leading limit.

The finite sum of nonnegative softplus weights is bounded by the summable total over primes. On the scale Z(P), the continuous reserve term tends to 2*c and the softplus sum tends to (pi^2/6)/c. The logarithmic correction from the p-series in the Rankin majorant is bounded for s at least two, so its ratio to Z(P) tends to zero. The two leading coefficients sum to 2*pi/sqrt(3).

This is the bound of Proposition 7.5 in the theory of the LCM-power Robin kappa threshold.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper.sharp_upper_bound`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTail/FarDeletion](FarDeletion.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/MovingPrimeSoftplus](../../PriceRecord/MovingPrimeSoftplus.md)
