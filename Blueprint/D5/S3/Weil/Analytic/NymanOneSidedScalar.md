# One-sided Landau continuation for Möbius shells

## Abstract

One-sided Landau continuation for Möbius shells

**Theorem 1.1 (Mellin transform of the logarithmic shell signal).**

Lean statement: `D5/S3/Weil/Analytic/NymanOneSidedScalar.signal_mellin`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanOneSidedScalar.signal_mellin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real kernel W vanishing outside (1, 2), the real logarithmic shell signal uses scale 2 exp(−t). Its Laplace integral over t > 0 multiplied by 2^s equals the Mellin transform of the Möbius dilates of W. The dilates vanish at scales at least 2, so the substitution covers the whole nonzero part of the Mellin integral. The identity uses totalized integrals. For continuous Lipschitz kernels, the Laplace integral converges when Re(s) > 1.

**Theorem 1.2 (One-sided growth bounds exclude zeta zeros).**

Lean statement: `D5/S3/Weil/Analytic/NymanOneSidedScalar.zero_re_le_of_one_sided_signal`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Analytic/NymanOneSidedScalar.zero_re_le_of_one_sided_signal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be a continuous real kernel vanishing outside (1, 2), with Lipschitz constant K ≥ 0. For 0 < β < 1 and c ≠ 0, suppose c times its logarithmic shell signal is eventually at most C exp(βt). Every zeta zero ρ with Re(ρ) < 1 and nonzero Mellin transform of W at ρ then has Re(ρ) ≤ β. After exponential normalization, positive Laplace continuation gives a holomorphic function on Re(s) > β. Multiplying by normalized zeta extends the numerator identity to that half-plane and forces the numerator to vanish at any zero there.

## References

- Truth anchor: `D5/S3/Weil/Analytic/NymanOneSidedScalar.signal_mellin`
- Truth anchor: `D5/S3/Weil/Analytic/NymanOneSidedScalar.zero_re_le_of_one_sided_signal`
- Dependency: [D5/S3/Analytic/Isolation/RiemannZetaPositiveRealSign](../../Analytic/Isolation/RiemannZetaPositiveRealSign.md)
- Dependency: [D5/S3/Analytic/Laplace/PositiveLaplaceContinuation](../../Analytic/Laplace/PositiveLaplaceContinuation.md)
- Dependency: [D5/S3/Weil/Analytic/NymanShellMellin](NymanShellMellin.md)
- Dependency: [D5/S3/Weil/Analytic/NymanShellScale](NymanShellScale.md)
