# Finite Prime Observation Posterior

## Abstract

Finite prime observations freeze only the observed zeta coordinates.

**Theorem 1.1 (Finite prime observations preserve the unobserved posterior).**

$$1 < s \Rightarrow \left(\operatorname{IndependentObservedAndUnobservedCylinders}\left(s, S, k\right) \land \left(N = \operatorname{Product}\left(\operatorname{observedPrimeFactor}\left(S, k\right), \operatorname{unobservedCofactor}\left(S, k, N\right)\right) \land \left(\operatorname{CoprimeToObservedPrimeProduct}\left(S, k, N\right) \land \operatorname{PreservesEveryUnobservedExponent}\left(S, k, N\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/FinitePrimeObservationPosterior.finite_prime_observation_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a zeta exponent above one, a finite set of observed primes, and their exponent readings. Every finite exponent cylinder on a disjoint prime set is independent of the observed cylinder.

For every nonzero integer realizing those readings, the observed prime powers form the known factor. The canonical quotient reconstructs the integer, is coprime to the product of the observed primes, and has the original exponent at every unobserved prime.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/FinitePrimeObservationPosterior.finite_prime_observation_posterior`
