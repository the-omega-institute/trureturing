# Cayley-Cauchy Limit

## Abstract

Uniform finite cyclic phases converge weakly under the Cayley chart to the standard Cauchy probability measure.

**Theorem 1.1 (Finite cyclic Haar phases have the standard Cauchy limit).**

$$\operatorname{Tendsto}\left(cayleyCauchyEmpirical, atTop, \operatorname{nhds}\left(standardCauchyProbabilityMeasure\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/CayleyCauchyLimit.cayley_cauchy_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For modulus K=n+2, cyclicHaarPhase n is the uniform probability measure on the scaled integral-lattice phases j/K with 1 <= j < K. The empirical law is its pushforward by cayleyPhase(u)=tan(pi(u-1/2))=-cot(pi u).

As n tends to infinity, these probability measures converge in Mathlib's weak topology to standardCauchyProbabilityMeasure, the canonical cauchyMeasure 0 1 with density dh/(pi(1+h^2)). This is one weak-convergence assertion; the supporting interval counts and CDF identities are not stated as additional conclusions.

## References

- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/CayleyCauchyLimit.cayley_cauchy_limit`
