# Relative Prime Density and Evidence Divergence

## Abstract

Relative prime density zero does not force evidence summability.

**Definition 1.1 (Natural numbers enumerate the primes).**

$$N \equiv NatPrimes$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.primeIndexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The increasing prime enumeration is packaged with its inverse prime index, so prime-relative counting can be expressed on natural indices.

**Definition 1.2 (Relative prime counting ratio).**

$$\operatorname{r}\left(S, n\right) = \frac{\lvert k < n \mid \operatorname{primeIndexEquiv}\left(k\right) \in S \rvert}{n}$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.relativePrimeCountingRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio counts selected prime indices in the first n entries of the prime enumeration and divides by n.

**Definition 1.3 (Square-indexed prime support).**

$$Ssq = \{\operatorname{primeIndexEquiv}\left(\operatorname{square}\left(k\right)\right) \mid k \in N\}$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.squareIndexedPrimeSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The selected support consists of primes at square natural indices. Its first n members are bounded by the square-root scale.

**Definition 1.4 (Harmonic evidence on square-indexed primes).**

$$\operatorname{esq}\left(p\right) = \operatorname{piecewise}\left(p \in Ssq, \frac{1}{(\operatorname{sqrt}\left(\operatorname{index}\left(p\right)\right) + 1)}, 0\right)$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.squareIndexedPrimeEvidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A square-indexed prime receives the reciprocal of its square-root index plus one; every other prime receives zero.

**Theorem 1.5 (Every relative ratio is zero at the zero cutoff).**

$$\forall S, \operatorname{r}\left(S, 0\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.relativePrimeCountingRatio_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At n equal to zero the counted range is empty and the totalized ratio is exactly zero.

**Theorem 1.6 (Empty support has relative density zero).**

$$\lim_{n\to\infty} \operatorname{r}\left(\emptyset, n\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.empty_relative_prime_density_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty support gives the constant zero ratio. This is the explicit zero-density boundary witness.

**Theorem 1.7 (Full support has relative density one).**

$$\lim_{n\to\infty} \operatorname{r}\left(univ, n\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.full_relative_prime_density_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The universal support contains every enumerated prime, so its ratio is one away from the totalized zero cutoff.

**Theorem 1.8 (Singleton support is density zero and summable).**

$$\forall q, s, \lim_{n\to\infty} \operatorname{r}\left(\{q\}, n\right) = 0 \land Summable\left(\operatorname{e}\left(\{q\}, s\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.singleton_relative_prime_density_zero_and_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A singleton prime support has zero relative density and only one possible nonzero evidence term, for every real exponent.

**Theorem 1.9 (Square-indexed support has relative density zero).**

$$\lim_{n\to\infty} \operatorname{r}\left(Ssq, n\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.square_indexed_prime_support_relative_density_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square support has at most square-root many hits among the first n prime indices, so its relative prime density tends to zero.

**Theorem 1.10 (Square-indexed harmonic evidence is divergent).**

$$\neg Summable\left(esq\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.square_indexed_prime_evidence_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Restricting the evidence to square indices exposes the harmonic series along an injective prime subsequence.

**Theorem 1.11 (Zero relative density can carry divergent evidence).**

$$\lim_{n\to\infty} \operatorname{r}\left(Ssq, n\right) = 0 \land \neg Summable\left(esq\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.zero_relative_prime_density_with_divergent_evidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square-indexed support simultaneously witnesses zero relative prime density and nonsummable cumulative evidence.

**Theorem 1.12 (Relative prime density does not determine summability).**

$$countingDensityContrast \land \left(\lim_{n\to\infty} \operatorname{r}\left(Ssq, n\right) = 0 \land \neg Summable\left(esq\right) \land \left(\lim_{n\to\infty} \operatorname{r}\left(univ, n\right) = 1 \land Summable\left(primeEvidence2\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.prime_relative_density_does_not_determine_evidence_summability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem combines the earlier natural-density contrast with the new zero-relative-density divergent example and the full-density convergent witness.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.empty_relative_prime_density_zero`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.full_relative_prime_density_one`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.primeIndexEquiv`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.prime_relative_density_does_not_determine_evidence_summability`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.relativePrimeCountingRatio`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.relativePrimeCountingRatio_zero`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.singleton_relative_prime_density_zero_and_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.squareIndexedPrimeEvidence`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.squareIndexedPrimeSupport`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.square_indexed_prime_evidence_not_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.square_indexed_prime_support_relative_density_zero`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeRelativeDensityEvidenceDivergence.zero_relative_prime_density_with_divergent_evidence`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality](PrimeDensityEvidenceOrthogonality.md)
