# Cayley-Laguerre Moment Tomography

## Abstract

Scaled Laguerre kernels recover even Cayley moments and control finite windows.

**Theorem 1.1 (Cayley-Laguerre identity).**

$$\forall n \in \operatorname{Natural}\left(\right), a \in \operatorname{Real}\left(\right), xi \in \operatorname{Real}\left(\right),\; \left(1 \le n \land 0 < a\right) \Rightarrow \operatorname{pow}\left(\operatorname{cayleyCharacter}\left(a, xi\right), n\right) = 1 - \operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{laguerreKernel}\left(n, a, t\right)\right) \cdot \operatorname{exp}\left(\operatorname{neg}\left(\operatorname{I}\left(\right) \cdot xi \cdot t\right)\right), \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioi}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.cayley_laguerre_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive scale and positive natural order, the all-pass Cayley power is one minus the negative-sign Fourier transform of the causal scaled Laguerre kernel. The kernel is constructed from the repository's canonical generalized Laguerre finite sum.

**Theorem 1.2 (Laguerre moment tomography).**

$$\forall rho \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), n \in \operatorname{Natural}\left(\right), a \in \operatorname{Real}\left(\right),\; \left(\operatorname{IsFiniteMeasure}\left(rho\right) \land \left(\operatorname{map}\left(\operatorname{lambda}\left(xi, \operatorname{neg}\left(xi\right)\right), rho\right) = rho \land \left(1 \le n \land 0 < a\right)\right)\right) \Rightarrow \left(\operatorname{cayleyMoment}\left(rho, n, a\right) = \operatorname{complex}\left(\operatorname{spectralMass}\left(rho\right)\right) - \operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{laguerreKernel}\left(n, a, t\right)\right) \cdot \operatorname{resolventCorrelation}\left(rho, t\right), \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioi}\left(0\right)\right)\right) \land \operatorname{cayleyMoment}\left(rho, n, a\right) = \operatorname{complex}\left(\operatorname{spectralMass}\left(rho\right)\right) - \operatorname{complex}\left(2 \cdot a\right) \cdot \operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{complex}\left(\operatorname{exp}\left(\operatorname{neg}\left(a \cdot t\right)\right) \cdot \operatorname{laguerreOne}\left(n - 1, 2 \cdot a \cdot t\right)\right) \cdot \operatorname{resolventCorrelation}\left(rho, t\right), \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioi}\left(0\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.laguerre_moment_tomography` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let rho be a finite even positive measure on the real line. Both source equalities are public: first in named kernel form and then with the factor 2a and the generalized Laguerre polynomial displayed. Evenness identifies the negative-sign Fourier integral with the positive-sign resolvent correlation.

**Theorem 1.3 (Finite-window moment tube).**

$$\forall rho \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), n \in \operatorname{Natural}\left(\right), a \in \operatorname{Real}\left(\right), L \in \operatorname{Real}\left(\right),\; \left(\operatorname{IsFiniteMeasure}\left(rho\right) \land \left(\operatorname{map}\left(\operatorname{lambda}\left(xi, \operatorname{neg}\left(xi\right)\right), rho\right) = rho \land \left(1 \le n \land \left(0 < a \land 0 \le L\right)\right)\right)\right) \Rightarrow \operatorname{norm}\left(\operatorname{cayleyMoment}\left(rho, n, a\right) - \operatorname{windowMoment}\left(rho, n, a, L\right)\right) \le \operatorname{spectralMass}\left(rho\right) \cdot \operatorname{laguerreTail}\left(n, a, L\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.finite_window_moment_tube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a nonnegative window length, subtracting the truncated estimator leaves exactly the kernel-correlation tail. The norm of every correlation value is bounded by the total spectral mass, giving the displayed mass-times-tail estimate.

**Theorem 1.4 (Moment affine budget law).**

$$\forall n \in \operatorname{Natural}\left(\right), a \in \operatorname{Real}\left(\right), L \in \operatorname{Real}\left(\right), H0 \in \operatorname{Real}\left(\right) \to \operatorname{Real}\left(\right), R \in \operatorname{Real}\left(\right),\; \left(0 < a \land \operatorname{ContinuousOn}\left(H0, \operatorname{Icc}\left(0, 2 \cdot L\right)\right)\right) \Rightarrow let A: \operatorname{Real}\left(\right) = \operatorname{neg}\left(\operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{laguerreKernel}\left(n, a, t\right) \cdot H0\left(t\right), \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioc}\left(0, 2 \cdot L\right)\right)\right)\right); let B: \operatorname{Real}\left(\right) = 1 - \operatorname{integral}\left(t, \operatorname{Real}\left(\right), \operatorname{laguerreKernel}\left(n, a, t\right) \cdot \operatorname{cosh}\left(a \cdot t\right), \operatorname{restrict}\left(\operatorname{volume}\left(\right), \operatorname{Ioc}\left(0, 2 \cdot L\right)\right)\right); \operatorname{budgetWindowMoment}\left(n, a, L, H0, R\right) = A + B \cdot R$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.moment_affine_budget_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The particular correlation H0 is real-valued and continuous on the finite window, as supplied by the local second-order equation in the source. The estimator is constructed from H0 plus R cosh(at). The displayed definitions of A and B are literal finite-window integrals, and integral linearity proves the affine equality.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.cayley_laguerre_identity`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.finite_window_moment_tube`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.laguerre_moment_tomography`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography.moment_affine_budget_law`
- Dependency: [D5/S3/Analytic/LiCausalTrichotomy](../../Analytic/LiCausalTrichotomy.md)
