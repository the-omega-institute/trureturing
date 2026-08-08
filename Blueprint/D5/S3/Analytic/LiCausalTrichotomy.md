# The Li-Test Causal Trichotomy

## Abstract

The Li symbol is causal exactly at integral index, equivalently when Cayley monodromy vanishes.

**Theorem 1.1 (Causality, integrality, and monodromy are equivalent).**

$$\kappa\ge 0:\quad \operatorname{CausalRealization}(\kappa)\Leftrightarrow \kappa\in\mathbb{N}\Leftrightarrow e^{2\pi i\kappa}=1,\qquad \Delta_0\left(z^\kappa-1\right)=2i\sin(\pi\kappa),\qquad \ell_\kappa(u)\sim\frac{\sin(\pi\kappa)}{\pi u}\ \ (u\to\pm\infty).$$

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/LiCausalTrichotomy.causal_iff_integer_iff_monodromy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the angular Fourier convention F(f)(gamma) = integral f(u) exp(i gamma u) du, obtained by reflecting the repository's canonical negative-sign kernel. For every nonnegative real kappa, an integrable inverse supported almost everywhere in u < 0 exists exactly when kappa is a natural number, and this is equivalent to exp(2 pi i kappa) = 1. At n = 0 both the symbol and packet are zero. For n >= 1 the inverse is exactly -1_{u<0} exp(u/2) L_{n-1}^{(1)}(-u), where L_m^{(1)} is the explicit standard finite sum, and its transform is z(gamma)^n - 1 for z(gamma) = (gamma + i/2)/(gamma - i/2).

At the Cayley branch cut, the right and left principal-log limits are exp(pi i kappa) - 1 and exp(-pi i kappa) - 1, so their difference is 2 i sin(pi kappa). For nonintegral kappa this jump is nonzero, while every L1 Fourier transform is continuous; therefore no causal L1 realization exists. The bounded scaled symbol nevertheless defines a tempered distribution, and inverse Fourier transform gives its canonical generalized inverse. Off zero, integration by parts separates the jump from the L1 transform of the symbol derivative. Riemann-Lebesgue then makes the remainder vanish and yields equivalence to sin(pi kappa)/(pi u) at both positive and negative infinity, hence eventual nonvanishing on both sides.

The finite Laguerre transform is computed term by term from complex Laplace moments and the binomial theorem. The result is analytic only: it asserts neither Li positivity nor the Riemann hypothesis, zero statistics, numerical certification, or physical causality.

## References

- Truth anchor: `D5/S3/Analytic/LiCausalTrichotomy.causal_iff_integer_iff_monodromy`
