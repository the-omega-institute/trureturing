# Euler Counterterm Uniqueness and the Pi Contrast

## Abstract

The Euler-Mascheroni constant is the unique finite harmonic-log counterterm, while pi eliminates the standard Gaussian Fourier self-duality defect.

**Theorem 1.1 (Gamma is the unique finite counterterm and pi removes the duality defect).**

$$[\forall c\in \mathbb{R}, [\lim_{n\to\infty} (H_n - \log n - c) = 0] \implies c = \gamma] \land\\{}[\lim_{n\to\infty} (H_n - \log n - \gamma) = 0] \land\\{}[\forall c\in \mathbb{R}, [\lim_{n\to\infty} (H_n - \log n - c) = 0] \implies c = \gamma] \land\\{}[\widehat{g_\pi} - g_\pi = 0].$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Limits/EulerCountertermUniqueness.euler_counterterm_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here H_n is the nth harmonic number. Pinned Mathlib proves that H_n minus log n tends to the Euler-Mascheroni constant, which supplies the zero-residual certificate. Adding any candidate counterterm back to its zero-residual limit and using uniqueness of real limits identifies that candidate with gamma. Both source occurrences of this conditional uniqueness are displayed separately.

For the source's pi contrast, g_a is exp(-a x^2), the Fourier transform is Mathlib's standard real transform with kernel exp(-2 pi i x xi), and the named defect is the transform of g_a minus g_a. The repository's Gaussian self-duality theorem proves that this defect vanishes at pi; the theorem does not replace the Fourier structure by a scalar proxy.

## References

- Truth anchor: `D5/S3/Constants/Limits/EulerCountertermUniqueness.euler_counterterm_unique`
- Dependency: [D5/S3/Fourier/CompletionConstants/GaussianSelfDualPi](../../Fourier/CompletionConstants/GaussianSelfDualPi.md)
