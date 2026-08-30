# Positive Lower Density Evidence Divergence

## Abstract

Positive lower prime density forces reciprocal evidence divergence.

**Definition 1.1 (Prime-relative counting ratio).**

$$r(S,n) = \frac{A(S,n)}{n}$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.primeRelativeCountingRatio` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ratio counts selected members among the first n primes.

**Definition 1.2 (Positive lower relative density).**

$$\exists m > 0, \forall n \to \infty, n \le m \cdot A(S,n)$$

*Formalization.* `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.HasPositiveLowerRelativeDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Eventually, selected prime indices occupy a fixed positive fraction.

**Theorem 1.3 (Every prime-relative ratio is zero at zero).**

$$r(S,0) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.primeRelativeCountingRatio_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At n equal to zero, totalized division makes every ratio zero.

**Theorem 1.4 (Empty support has zero relative ratio).**

$$\lim_{n\to\infty} r(\emptyset,n) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.empty_primeRelativeCountingRatio_tendsto_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty support has prime-relative counting ratio tending to zero.

**Theorem 1.5 (Empty support has no positive lower density).**

$$\neg PositiveLowerDensity\left(\emptyset\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.empty_not_hasPositiveLowerRelativeDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An eventually positive counting fraction excludes empty support.

**Theorem 1.6 (Full prime support has positive lower density).**

$$PositiveLowerDensity\left(P\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.primeNaturals_hasPositiveLowerRelativeDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All prime indices are selected, so the relative density is one.

**Theorem 1.7 (Restricted reciprocal evidence diverges).**

$$PositiveLowerDensity\left(S\right) \implies \neg Summable\left(e(S,1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.restricted_reciprocal_evidence_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive lower density yields a linear enumeration bound and divergence.

**Theorem 1.8 (An eventual reciprocal lower bound forces divergence).**

$$PositiveLowerDensity\left(S\right), c > 0, eventually(\frac{c}{p} \leq e) \implies \neg Summable\left(e\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.positive_lower_density_evidence_not_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive c over p lower bound transfers reciprocal divergence to e.

**Theorem 1.9 (Zero prime evidence is summable).**

$$Summable\left(0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.zero_prime_evidence_summable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant-zero family records the trivial-map degeneration.

**Theorem 1.10 (A positive coefficient is necessary).**

$$PositiveLowerDensity\left(P\right) \land \left(bound(0,P,0) \land Summable\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.positive_coefficient_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At c equal to zero, full support permits summable zero evidence.

**Theorem 1.11 (Positive lower density is necessary).**

$$\neg PositiveLowerDensity\left(\emptyset\right) \land \left(bound(1,\emptyset,0) \land Summable\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.positive_lower_density_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Empty support makes the lower bound vacuous and zero evidence summable.

**Theorem 1.12 (The reciprocal lower bound is necessary).**

$$PositiveLowerDensity\left(P\right) \land \left(\neg bound(1,P,0) \land Summable\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.reciprocal_lower_bound_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero evidence on full support violates the coefficient-one bound.

## References

- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.HasPositiveLowerRelativeDensity`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.empty_not_hasPositiveLowerRelativeDensity`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.empty_primeRelativeCountingRatio_tendsto_zero`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.positive_coefficient_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.positive_lower_density_evidence_not_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.positive_lower_density_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.primeNaturals_hasPositiveLowerRelativeDensity`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.primeRelativeCountingRatio`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.primeRelativeCountingRatio_zero`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.reciprocal_lower_bound_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.restricted_reciprocal_evidence_not_summable`
- Truth anchor: `D5/S3/Analytic/ZetaEntropyPlane/PositiveLowerDensityEvidenceDivergence.zero_prime_evidence_summable`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeDensityEvidenceOrthogonality](PrimeDensityEvidenceOrthogonality.md)
