# Zero-Density Reciprocal Prime Evidence

## Abstract

A zero-relative-density prime set can carry divergent reciprocal mass and, under the product-law criterion, statistical completion.

**Theorem 1.1 (Sparse primes can retain divergent reciprocal evidence).**

$$\exists S \subseteq Primes, \lim_{n\to\infty} \operatorname{relativePrimeCountingRatio}\left(S, n\right) = 0 \land \left(\neg \operatorname{Summable}\left((p: S \mapsto \frac{1}{p})\right) \land \forall e, mu, nu, \left(mu \perp nu \Leftrightarrow \neg \operatorname{Summable}\left(e\right)\right) \Rightarrow \left(\operatorname{IsTheta}\left((p: S \mapsto e(p)), cofinite, (p: S \mapsto \frac{1}{p})\right) \Rightarrow mu \perp nu\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/ZeroDensityReciprocalPrimeSet.zero_density_divergent_reciprocal_prime_set` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one subset of the primes whose relative counting ratio tends to zero while its reciprocal-prime family is not summable.

The Lean witness is a classical, noncomputable selection: its block endpoints use Nat.find on analytic existence of enough reciprocal mass. It is not a computable enumeration of the subset.

For the same subset, evidence asymptotic to one over p yields mutually singular transcript laws under the singularity-versus-divergent-energy equivalence from the source's Theorem 233.1. No separate absolute-continuity-versus-summability premise is assumed.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/ZeroDensityReciprocalPrimeSet.zero_density_divergent_reciprocal_prime_set`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence](PrimeRelativeDensityEvidenceDivergence.md)
