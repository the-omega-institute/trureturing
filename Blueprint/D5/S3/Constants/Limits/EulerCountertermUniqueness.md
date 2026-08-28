# Euler Counterterm Uniqueness

## Abstract

The Euler-Mascheroni constant is the unique finite counterterm for the harmonic-logarithmic residual.

**Theorem 1.1 (A vanishing residual uniquely determines the counterterm).**

$$\forall c\in \mathbb{R},\\(\lim_{n\to\infty} (H_n - \log n - c) = 0) \Rightarrow c = \gamma.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Limits/EulerCountertermUniqueness.euler_counterterm_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The premise says that subtracting c from H_n - log n leaves a sequence tending to zero. Adding c back gives a second limit of the canonical harmonic-logarithmic sequence.

Mathlib proves that the same sequence tends to the Euler-Mascheroni constant. Uniqueness of limits in the real topology identifies the two constants.

## References

- Truth anchor: `D5/S3/Constants/Limits/EulerCountertermUniqueness.euler_counterterm_unique`
