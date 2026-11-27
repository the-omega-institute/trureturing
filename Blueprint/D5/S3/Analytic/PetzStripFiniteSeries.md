# Finite complex overlaps on the Petz strip

## Abstract

The weighted boundary deficits of a finite complex exponential overlap recover its negative real derivative at zero.

Let F(z) be the finite sum of c(i) exp(omega(i) z) with complex coefficients and real frequencies. Define each boundary deficit at real part a and imaginary part s to be 2(1 - Re F(a + i s)). The real parts of the left and right edges are zero and one half.

**Theorem 1.1 (Derivative of the finite overlap).**

Lean statement: `D5/S3/Analytic/PetzStripFiniteSeries.hasDerivAt_finiteOverlap_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzStripFiniteSeries.hasDerivAt_finiteOverlap_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complex derivative of F at zero is the finite sum of c(i) omega(i). Zero frequencies contribute zero.

**Theorem 1.2 (Two integrable boundary deficits).**

Lean statement: `D5/S3/Analytic/PetzStripFiniteSeries.integral_finiteOverlap_strip`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzStripFiniteSeries.integral_finiteOverlap_strip` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tai-Hsuan Yang (2026). *Quantum data processing equality*. DOI: [10.48550/arXiv.2609.33815](https://doi.org/10.48550/arXiv.2609.33815). URL: <https://arxiv.org/abs/2609.33815v2>.

*Commentary.*

Assume Re F(0) = 1 and the lower boundary deficit is nonnegative at every real s. The deficits multiplied respectively by pi/(cosh(2 pi s) - 1) and pi/(cosh(2 pi s) + 1) are each Lebesgue integrable on the whole line. Their integrals sum to the negative real part of the complex derivative at zero.

Yang's Lemma III.1, Eq. (III.2), gives the strip weights and boundary derivative formula for bounded harmonic functions with quadratic vanishing at the lower point. The repository proves integrability and the identity for finite exponential overlaps. Normalization and lower nonnegativity give quadratic vanishing at the singular lower point, where the reflection average dominates the actual deficit after weighting. On the upper line, finite exponential magnitudes bound the full deficit in absolute value and the Poisson weight is integrable. Reflection cancels the imaginary-coefficient sine terms in the two integrals. The upper cosine transform follows by dilating the compensated lower mode.

## References

- Truth anchor: `D5/S3/Analytic/PetzStripFiniteSeries.hasDerivAt_finiteOverlap_zero`
- Truth anchor: `D5/S3/Analytic/PetzStripFiniteSeries.integral_finiteOverlap_strip`
- Dependency: [D5/S3/Analytic/PetzCothStripMode](PetzCothStripMode.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzExponentialBoundaryEvaluation](../Quantum/Recovery/PetzExponentialBoundaryEvaluation.md)
