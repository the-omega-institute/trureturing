---
bibkey: connesvansuijlekom2025quadratic
authors: Alain Connes, Walter D. van Suijlekom
year: 2025
title: Quadratic Forms, Real Zeros and Echoes of the Spectral Action
doi: 10.1007/s00220-025-05493-1
url: https://www.waltervansuijlekom.nl/publications/quadratic-forms-real-zeros-and-echoes-of-the-spectral-action/
claim: A simple isolated even ground state of the stated distributional operator has a Fourier transform with only real zeros. The conditional approximation estimate needs a true gap and ground-vector approximation, and the source's explicit negative example prevents interpreting real Fourier zeros as original-form positivity.
strata_touched: []
license: citation-only
triage: anchor
---

# Ground-state approximation and the sign boundary

The primary text is the [published typeset PDF hosted by the author](https://www.waltervansuijlekom.nl/wp-content/uploads/2025/12/Araki-publCMP.pdf), *Communications in Mathematical Physics* 406:312 (2025), DOI [10.1007/s00220-025-05493-1](https://doi.org/10.1007/s00220-025-05493-1). The inspected PDF has 35 pages and SHA-256 `e9e5e9db037cffd403c28cafc5e653b8cafd4b0cbc5ed870ea71b4c74be0ab79`. Selected statements and their hypotheses were checked in that text; this note does not independently audit the paper's complete proofs or implement them in Lean.

## The reusable conditional theorem

Theorem 6.1, pp.17–18, starts with a real one-sided distribution $D$ on $[0,\ell]$, $\ell>0$, and the quadratic form defined on trigonometric polynomials by equation (6). It assumes a lower-bounded essentially selfadjoint operator on that core and a simple isolated spectral minimum $\mu$ with even eigenfunction $\xi$. Evenness here means symmetry about the midpoint of the source interval; after centering it is ordinary reflection symmetry. The theorem concludes that the entire Fourier transform of $\xi$ has only real zeros.

The proof normalizes $\|\xi\|=1$ and uses an even unit polynomial $\eta_\varepsilon$ satisfying

$$
\|\xi-\eta_\varepsilon\|<\varepsilon,
\qquad Q(\eta_\varepsilon)<\mu+\varepsilon.
$$

Let the true gap above $\mu$ be $\delta>0$, and take a section containing this polynomial. For $\varepsilon<\delta/2$ the proof obtains

$$
\mu\le\mu_N\le\mu+\varepsilon,
\qquad
\|\xi-\xi_N\|\le\varepsilon+\sqrt{\varepsilon/\delta}.
$$

The scale of $\xi_N$ in this inequality is the source's choice $\xi_N=P_N^{\mathrm{ground}}\eta_\varepsilon$, not an independently imposed unit normalization. The source supplies no computable $N(\varepsilon,L)$ or certified actual-Weil gap. Its polynomial approximation already refers to the unknown ground eigenfunction and energy. A form core alone is not the theorem's stated operator-core hypothesis.

Remark 4.3, p.11, also requires the one-sided distribution and its endpoint data to be retained: starting only from an even symmetrized distribution can lose information at the endpoint. A proposed Weil application must verify that interface, rather than identify distributions by their interior kernels alone.

## A published obstruction to reversing the conclusion

Appendix A, Proposition A.3, p.23, gives the operator

$$
(Mv)(x)=2\pi\int_0^1
\operatorname{sgn}(x-y)\sin(2\pi(x-y))v(y)\,dy.
$$

Fact A.4 and Proposition A.5, p.24, identify the extremal functions and state the maximum and minimum as $8/3$ and $-8/5$. The stated negative eigenfunction $v(x)=\sin(3\pi x)$ has, after centering, Fourier transform

$$
\frac{6\pi\cos(z/2)}{9\pi^2-z^2}.
$$

Proposition A.5 states that this is entire with only real zeros; the apparent singularities at $\pm3\pi$ are removable. The negative eigenpair is already enough to prevent the inference “real Fourier zeros imply positivity of the original form.” No new computation of this example or proof of the source theorem is needed. This is a counterexample to that general implication, not a Weil-form or RH counterexample.

## Actual-Weil obligation

The [2026 spectral construction](connesconsanimoscovici2026spectral.md) specifies the remaining actual-ground-state and transform-comparison steps. This precursor can be applied after its core, simplicity, evenness and gap assumptions have been established for the relevant operator. It does not establish those assumptions or the sign of the original minimum. The remaining mathematical work is an actual-operator estimate or comparison; another proof of this conditional theorem would not advance that interface.
