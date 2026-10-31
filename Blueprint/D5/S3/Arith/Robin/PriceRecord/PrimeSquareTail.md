# Uniform Prime Reciprocal-Square Tail

## Abstract

The prime reciprocal-square tail has leading constant one uniformly in two real cutoffs.

**Theorem 1.1 (Uniform finite-tail asymptotic).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail.prime_square_tail_uniform`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail.prime_square_tail_uniform` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real epsilon>0 there are real C>1 and Y>1 such that for every pair of real cutoffs y,z with Y<=y and C*y<=z, the absolute difference between y*log(y)*sum over primes y<p<=z of 1/p^2 and one is strictly less than epsilon. The sum is literally over the prime filter of Finset.Ioc(floorNat(y),floorNat(z)); the lower endpoint is strict even when y is an integer prime. Both thresholds precede both cutoff quantifiers. There is no theta-error hypothesis, RH hypothesis, record-integer restriction, or price parameter.

The PNT supplier EulerLayerRootCorrection.prime_number_limits gives theta(t)/t tending to one. The original finite_theta_abel_upper in ActualPriceRecordPrimeStructure supplies the upper estimate (1+3*rho)/(y*log(y)) uniformly for every upper cutoff. For the new lower estimate, Mathlib's exact real-endpoint Abel identity with coefficients log(p) at primes and zero elsewhere yields sum log(p)/p^2 >= (1-3*rho)/y-(1-rho)/z. The negative derivative reverses the lower theta comparison in the integral, and both endpoint corrections are retained.

Choose eta=min(epsilon/16,1/16) and C=1/eta. On (y,C*y], log(p)<=log(C*y), so the weighted lower bound implies a normalized unweighted bound at least (1-4*eta)*log(y)/log(C*y). Requiring Y>=exp(log(C)/eta) and Y>=2 makes log(y)/log(C*y) at least 1-eta; hence the normalized sum is at least 1-5*eta. Nonnegative summands and floor monotonicity extend it to every z>=C*y. The upper bound is 1+3*eta, giving the stated strict tolerance.

This is a repository derivation from the classical PNT and Abel summation. No literature novelty is claimed. It supplies a generic analytic input for the actual-record Euler-deficit leading constant; that further arithmetic application and RH are not conclusions of this theorem.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/PrimeSquareTail.prime_square_tail_uniform`
- Dependency: [D5/S3/Arith/Robin/ActualPriceRecordPrimeStructure](../ActualPriceRecordPrimeStructure.md)
