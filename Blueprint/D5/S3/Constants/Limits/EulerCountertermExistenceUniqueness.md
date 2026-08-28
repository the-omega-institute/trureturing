# Euler Counterterm Existence and the Pi Contrast

## Abstract

Euler's constant supplies the finite harmonic-log counterterm, while pi eliminates the standard Gaussian Fourier self-duality defect.

**Theorem 1.1 (Gamma supplies the counterterm and pi removes the duality defect).**

$$[\lim_{n\to\infty} (H_n - \log n - \gamma) = 0] \land\\{}[\widehat{g_\pi} - g_\pi = 0].$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Limits/EulerCountertermExistenceUniqueness.euler_counterterm_exists_and_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinned Mathlib proves that H_n minus log n tends to the Euler-Mascheroni constant. Subtracting that concrete constant therefore leaves a sequence tending to zero.

For the second conjunct, g_pi is the real Gaussian exp(-pi x^2), and its defect is its standard real Fourier transform minus itself. The repository's Gaussian self-duality theorem makes that defect zero.

## References

- Truth anchor: `D5/S3/Constants/Limits/EulerCountertermExistenceUniqueness.euler_counterterm_exists_and_unique`
- Dependency: [D5/S3/Fourier/CompletionConstants/GaussianSelfDualPi](../../Fourier/CompletionConstants/GaussianSelfDualPi.md)
