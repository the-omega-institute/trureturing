# Restricted Zeta Posterior

## Abstract

A single observed prime leaves a restricted zeta posterior.

**Theorem 1.1 (The restricted partition splits the Euler product).**

$$1 < s \Rightarrow \operatorname{RestrictedZetaEulerProduct}\left(s, p\right) = \operatorname{RiemannZetaTimesRemovedPrimeFactor}\left(s, p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.restricted_zeta_euler_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Above one, removing one prime factor from the full Euler product gives the restricted zeta normalizer.

**Theorem 1.2 (One observed exponent leaves a restricted zeta conditional law).**

$$\left(1 < s \land \operatorname{Coprime}\left(m, p\right)\right) \Rightarrow \operatorname{ConditionalMass}\left(\operatorname{ZetaLaw}\left(s\right), \operatorname{PrimeObservation}\left(p, k\right), \operatorname{Cofactor}\left(p, k, m\right)\right) = \frac{\operatorname{Weight}\left(s, m\right)}{\operatorname{RestrictedZetaPartition}\left(s, p\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.single_prime_restricted_zeta_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a concrete zeta law, conditioning on one prime exponent leaves the coprime cofactor with its restricted normalizer.

**Theorem 1.3 (The empty observation recovers the original zeta point mass).**

$$1 < s \Rightarrow \operatorname{ConditionalMass}\left(\operatorname{ZetaLaw}\left(s\right), \operatorname{EmptyObservation}\left(\right), \operatorname{Singleton}\left(m\right)\right) = \frac{\operatorname{Weight}\left(s, m\right)}{\operatorname{Partition}\left(s\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.empty_prime_observation_recovers_zeta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With no observed primes, the conditional law is the unconditioned zeta point mass.

**Theorem 1.4 (A zero cofactor has zero conditional mass).**

$$1 < s \Rightarrow \operatorname{ConditionalMass}\left(\operatorname{ZetaLaw}\left(s\right), \operatorname{PrimeObservation}\left(p, k\right), \operatorname{ZeroCofactor}\left(p, k\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.single_prime_zero_cofactor_posterior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every observed positive prime power makes the zero cofactor event a null event under the zeta law.

**Theorem 1.5 (The restricted zeta normalizer is nonzero).**

$$1 < s \Rightarrow \operatorname{RestrictedZetaPartition}\left(s, p\right) \ne 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.restricted_zeta_partition_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prime and exponent above one, the restricted normalizer is strictly positive and hence nonzero.

**Theorem 1.6 (The exponent threshold is necessary for normalization).**

$$\operatorname{Partition}\left(1\right) = \infty$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.zeta_exponent_above_one_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent one, the integer partition function is infinite, so the strict threshold cannot be dropped.

**Theorem 1.7 (Coprimality is necessary for the cofactor reconstruction).**

$$\operatorname{PrimeObservationCofactorIntersection}\left(2, 0, 2\right) = \operatorname{EmptySet}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.coprimality_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At prime two, the exponent-zero observation and cofactor two are incompatible, exhibiting the missing coprimality hypothesis.

**Theorem 1.8 (The zero reading and unit cofactor specialize correctly).**

$$1 < s \Rightarrow \operatorname{ConditionalMass}\left(\operatorname{ZetaLaw}\left(s\right), \operatorname{PrimeObservation}\left(p, 0\right), \operatorname{Cofactor}\left(p, 0, 1\right)\right) = \frac{\operatorname{Weight}\left(s, 1\right)}{\operatorname{RestrictedZetaPartition}\left(s, p\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.restricted_zeta_posterior_at_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The k equals zero and m equals one specialization is an explicit degenerate audit of the single-prime posterior.

**Theorem 1.9 (A finite observation cannot contain every prime).**

$$\neg \operatorname{FinitePrimeSetContainsAllPrimes}\left(\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.no_finite_observation_contains_all_primes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The all-primes observation is unavailable for a finite prime budget, so that proposed degeneration is excluded.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.coprimality_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.empty_prime_observation_recovers_zeta`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.no_finite_observation_contains_all_primes`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.restricted_zeta_euler_split`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.restricted_zeta_partition_ne_zero`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.restricted_zeta_posterior_at_unit`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.single_prime_restricted_zeta_posterior`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.single_prime_zero_cofactor_posterior`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/RestrictedZetaPosterior.zeta_exponent_above_one_is_necessary`
- Dependency: [D5/S3/Analytic/ZetaObservation/FinitePrimeObservationPosterior](FinitePrimeObservationPosterior.md)
