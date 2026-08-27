# Prime Density Does Not Determine Evidence Summability

## Abstract

Prime sparsity in the naturals is independent of evidence summability.

**Definition 1.1 (Natural counting ratio).**

$$r_{S}(n) = \frac{\lvert\{k:1 \leq k \leq n, k \in S\}\rvert}{n}$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.naturalCountingRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio counts members of a natural-number set between one and n, then divides by n. It is the explicit density surrogate used here.

**Definition 1.2 (Prime naturals).**

$$P = \{p \in \mathbb{N} \mid Prime(p)\}$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.primeNaturals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sparse natural-number support is the named set of all prime values.

**Definition 1.3 (Restricted prime evidence).**

$$e(S,s,p) = chi(S,p) \cdot e(P,s,p)$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.restrictedPrimeEvidence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction multiplies the existing prime evidence by the support indicator. Outside the selected natural values it is zero.

**Theorem 1.4 (Every counting ratio is zero at zero).**

$$\forall S, r_{S}(0) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.naturalCountingRatio_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interval is empty at n equal to zero, and totalized division returns zero. This records the endpoint degeneration explicitly.

**Theorem 1.5 (Prime support has the prime-counting ratio).**

$$\forall n, r_{P}(n) = \frac{\pi(n)}{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.primeNaturals_countingRatio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Counting the named prime set through n gives the usual prime-counting function, divided by n.

**Theorem 1.6 (Sparse prime support has divergent reciprocal evidence).**

$$\lim_{n\to\infty} r_{P}(n) = 0 \land \neg Summable\left(e(P,1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.sparse_prime_support_diverges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Chebyshev's bound makes the prime counting ratio vanish in the naturals. Euler's reciprocal-prime theorem still makes exponent one diverge.

**Theorem 1.7 (Full prime support has summable square evidence).**

$$(\forall p: Primes, p \in P) \land Summable\left(e(P,2)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.full_prime_support_square_evidence_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same support contains every prime, so it is full relative to the prime subtype. Exponent two is summable by the imported threshold theorem.

**Theorem 1.8 (Empty support is sparse and summable).**

$$\lim_{n\to\infty} r_{\emptyset}(n) = 0 \land Summable\left(e(\emptyset,1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.empty_support_sparse_and_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Empty support also has zero counting ratio, but its restricted evidence is the zero family and is summable. Zero density permits both outcomes.

**Theorem 1.9 (Singleton prime support is summable).**

$$\forall q, s, Summable\left(e(\{q\},s)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.singleton_prime_support_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A one-prime support has only one possibly nonzero term, so it is summable for every real exponent.

**Theorem 1.10 (Counting density does not determine summability).**

$$\left(\lim_{n\to\infty} r_{P}(n) = 0 \land \neg Summable\left(e(P,1)\right)\right) \land \left(\left((\forall p: Primes, p \in P) \land Summable\left(e(P,2)\right)\right) \land \left(\lim_{n\to\infty} r_{\emptyset}(n) = 0 \land Summable\left(e(\emptyset,1)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.counting_density_not_sufficient_for_summability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The combined statement records sparse divergence, full-support square convergence, and empty-support convergence in one public theorem.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.counting_density_not_sufficient_for_summability`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.empty_support_sparse_and_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.full_prime_support_square_evidence_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.naturalCountingRatio`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.naturalCountingRatio_zero`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.primeNaturals`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.primeNaturals_countingRatio`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.restrictedPrimeEvidence`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.singleton_prime_support_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality.sparse_prime_support_diverges`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold](PrimeEvidenceSharpThreshold.md)
