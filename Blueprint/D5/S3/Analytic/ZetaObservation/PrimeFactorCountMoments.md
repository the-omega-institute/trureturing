# Moments of the Distinct Prime-Factor Count

## Abstract

The zeta-law distinct-prime count has the exact Bernoulli mean and variance.

**Definition 1.1 (The distinct prime-factor count reuses Mathlib omega).**

$$\operatorname{PrimeFactorCount}\left(n\right) = \operatorname{omega}\left(n\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.primeFactorCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The named wrapper exposes FPOD's distinct-prime count while retaining Mathlib's totalized values at zero and one.

**Definition 1.2 (A prime-support coordinate is a real indicator).**

$$\operatorname{PrimeSupportIndicator}\left(p, n\right) = \operatorname{indicator}\left(0 < \operatorname{factorExponent}\left(n, p\right)\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.primeSupportIndicator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate is one exactly when the selected prime has positive factorization exponent, and zero otherwise.

**Theorem 1.3 (The count is the pointwise sum of support indicators).**

$$\operatorname{PrimeFactorCount}\left(n\right) = \sum_{p\in \mathbb{P}} \operatorname{PrimeSupportIndicator}\left(p, n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.primeFactorCount_eq_tsum_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural number, factorization support is finite. The count is therefore the prime-indexed sum of its zero-one coordinates, including at zero and one.

**Theorem 1.4 (The zeta-law mean is the prime evidence sum).**

$$1 < s \Rightarrow \operatorname{ExpectationUnderZeta}\left(s, \operatorname{PrimeFactorCount}\left(N\right)\right) = \sum_{p\in \mathbb{P}} p^{{-s}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.prime_factor_count_expectation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the full zeta-law result, not the assumption-based fallback. The repository's zeta probability measure and Bernoulli support coordinates are reused.

Interchanging expectation and the countable sum uses the sharp summability theorem for the prime evidence series above one.

**Theorem 1.5 (The variance is the sum of Bernoulli variances).**

$$1 < s \Rightarrow \operatorname{VarianceUnderZeta}\left(s, \operatorname{PrimeFactorCount}\left(N\right)\right) = \sum_{p\in \mathbb{P}} p^{{-s}} \cdot {1 - p^{{-s}}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.prime_factor_count_variance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mutual independence comes from unique factorization through the existing prime-coordinate theorem. It is not a consequence of the index type merely being countable.

The second moment separates diagonal Bernoulli terms from products of distinct coordinates. Both resulting prime series are summable when the exponent is above one.

**Theorem 1.6 (Zero, one, and a prime realize the basic degeneracies).**

$$\operatorname{PrimeFactorCount}\left(0\right) = 0 \land \left(\operatorname{PrimeFactorCount}\left(1\right) = 0 \land \operatorname{PrimeFactorCount}\left(p\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.prime_factor_count_degenerate_audit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The count vanishes at zero and one and equals one at a prime. Empty and singleton finite support families are already covered by the mutual independence theorem used in the variance proof.

**Theorem 1.7 (Exponent one is a named nonsummable counterexample).**

$$\neg \operatorname{Summable}\left(p\mapsto p^{{-1}}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.moment_threshold_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At exponent one the reciprocal-prime evidence family is not summable, so the strict threshold in the moment theorems cannot be weakened to a non-strict inequality.

Prime distribution is load-bearing only for this analytic threshold. The Bernoulli moment algebra itself applies to any independent summable zero-one family.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.moment_threshold_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.primeFactorCount`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.primeFactorCount_eq_tsum_support`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.primeSupportIndicator`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.prime_factor_count_degenerate_audit`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.prime_factor_count_expectation`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/PrimeFactorCountMoments.prime_factor_count_variance`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold](../ZetaEntropyPlane/PrimeEvidenceSharpThreshold.md)
- Dependency: [D5/S3/Analytic/ZetaObservation/MultiplicativeComplexityActivation](MultiplicativeComplexityActivation.md)
- Dependency: [D5/S3/Analytic/ZetaObservation/PrimeSupportBernoulliIndependence](PrimeSupportBernoulliIndependence.md)
