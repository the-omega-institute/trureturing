# Global Code Length Additivity

## Abstract

A zeta sample's surprisal is the sum of its prime-coordinate code lengths.

**Definition 1.1 (Prime-coordinate code length).**

$$ell_{p,s}(k) = -log\left({1 - p^{{-s}}}\right) + s k log\left(p\right)$$

*Formalization.* `D5/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity.primeCodeLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At prime p, exponent k has the geometric baseline minus log of one minus p to the power minus s, plus the occupied cost s k log p.

**Theorem 1.2 (Global code length adds over prime coordinates).**

$$\forall s, n, \left(1 < s \land 1 \le n\right) \Rightarrow -log\left(P_{s}(n)\right) = \sum_{p\in \mathbb{P}} ell_{p,s}(v_{p}(n))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity.global_code_length_additive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive sampled natural, its negative log zeta mass is the convergent sum of the local code lengths over all primes.

The common baseline is the logarithm of the Euler product. The occupied contribution is s log n by unique factorization.

**Theorem 1.3 (The positive-sample condition is necessary).**

$$-log\left(P_{2}(0)\right) \neq \sum_{p\in \mathbb{P}} ell_{p,2}(v_{p}(0))$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity.positive_sample_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At s equal to two and n equal to zero, the totalized negative log mass is zero, while the sum of the positive Euler baselines is positive.

## References

- Truth anchor: `D5/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity.global_code_length_additive`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity.positive_sample_is_necessary`
- Truth anchor: `D5/S3/Analytic/ZetaObservation/GlobalCodeLengthAdditivity.primeCodeLength`
- Dependency: [D5/S3/Analytic/ZetaEntropyPlane/PrimeEvidenceSharpThreshold](../ZetaEntropyPlane/PrimeEvidenceSharpThreshold.md)
- Dependency: [D5/S3/Factorization/LogarithmicLength](../../Factorization/LogarithmicLength.md)
