# Probability Generating Function of the Distinct Prime Count

## Abstract

The zeta-law distinct-prime count has a convergent probability generating product.

**Definition 1.1 (The distinct-prime probability generating function).**

$$\operatorname{PrimeFactorCountPGF}\left(s, z\right) := \operatorname{ExpectationUnderZeta}\left(s, z^{{\operatorname{PrimeFactorCount}\left(N\right)}}\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.primeFactorCountPGF` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The definition integrates z raised to the repository's canonical distinct-prime count under the zeta probability law.

**Definition 1.2 (One prime contributes one affine Euler factor).**

$$\operatorname{PrimeFactorCountEulerFactor}\left(s, z, p\right) := 1 - {1 - z} \cdot p^{{-s}}$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.primeFactorCountEulerFactor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local factor is the generating function of the imported Bernoulli prime-support coordinate.

**Theorem 1.3 (The prime-indexed Euler factors are multipliable).**

$$1 < s \Rightarrow \operatorname{Multipliable}\left(p \mapsto \operatorname{PrimeFactorCountEulerFactor}\left(s, z, p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.prime_factor_count_euler_factors_multipliable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Convergence follows from summability of the prime evidence family and does not otherwise use the distribution of the prime indices.

**Theorem 1.4 (The distinct-prime PGF equals its convergent Euler product).**

$$\left(1 < s \land \left(0 \le z \land z \le 1\right)\right) \Rightarrow \operatorname{PrimeFactorCountPGF}\left(s, z\right) = \prod_{p\in \mathbb{P}} \operatorname{PrimeFactorCountEulerFactor}\left(s, z, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.prime_factor_count_pgf_euler_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For zero through one, finite independent Bernoulli products converge under the integral to the full distinct-prime count.

The multiplicity-counting formula remains open because the source does not state its convergence domain.

**Theorem 1.5 (At one the PGF is total probability).**

$$1 < s \Rightarrow \operatorname{PrimeFactorCountPGF}\left(s, 1\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.prime_factor_count_pgf_at_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generating integrand is constantly one, so the endpoint is the total mass of the zeta probability law.

**Theorem 1.6 (At zero the PGF is the zeta mass of one).**

$$1 < s \Rightarrow \operatorname{PrimeFactorCountPGF}\left(s, 0\right) = \operatorname{ZetaMass}\left(s, 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.prime_factor_count_pgf_at_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The totalized count also vanishes at zero, but the zeta law assigns zero mass there; every natural above one has positive count.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.primeFactorCountEulerFactor`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.primeFactorCountPGF`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.prime_factor_count_euler_factors_multipliable`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.prime_factor_count_pgf_at_one`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.prime_factor_count_pgf_at_zero`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountGeneratingFunction.prime_factor_count_pgf_euler_product`
- Dependency: [D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments](PrimeFactorCountMoments.md)
