# Harmonic Residual Limit

## Abstract

The normalized harmonic residual converges to one minus the Euler-Mascheroni constant.

**Theorem 1.1 (The harmonic residual tends to one minus Euler's constant).**

$$\lim_{n\to\infty} [1 - (H_n - \log n)] = 1 - \gamma.$$

*Proof.* Machine-checked in Lean as `D5/S3/Constants/Limits/HarmonicResidualLimit.harmonic_residual_tendsto_one_sub_euler_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let H_n be the nth harmonic number. The pinned Mathlib theorem Real.tendsto_harmonic_sub_log proves that H_n - log n tends to the Euler-Mascheroni constant. Subtracting this convergent sequence from the constant sequence one gives the stated residual limit.

This is partial closure of the source atom's asymptotic residual clause. It does not formalize the protocol-cost interpretation, tracking rates, or the other numerical and information-theoretic claims in that atom.

## References

- Truth anchor: `D5/S3/Constants/Limits/HarmonicResidualLimit.harmonic_residual_tendsto_one_sub_euler_constant`
