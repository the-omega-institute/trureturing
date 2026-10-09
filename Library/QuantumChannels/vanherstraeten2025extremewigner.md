---
bibkey: vanherstraeten2025extremewigner
authors: Zacharie Van Herstraeten; Jack Davis; Nuno C. Dias; João N. Prata; Nicolas J. Cerf; Ulysse Chabaud
year: 2025
title: Extreme non-negative Wigner functions
doi: null
url: https://arxiv.org/abs/2512.14831v3
claim: Every beam-splitter state formed from two Fock-bounded pure inputs is an extreme Wigner-positive state.
strata_touched:
  - D5/S3/Quantum/QuantumChannels/FockAttenuator/FiniteFockBeamSplitterNonExtremality
license: citation-only
triage: anchor
---

# Extreme non-negative Wigner functions

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2512.14831v3

The Crossref title query “Extreme non-negative Wigner functions” has no exact
title match among its ten returned works. No publication DOI is asserted.

The locators below use the printed page numbers of version 3.

- Page 4, Definition 1 (Beam-splitter state): “A beam-splitter state $\hat{\sigma}$ is the single-mode output of a balanced beam-splitter acting on a separable state $\hat{\rho}_{\mathrm{sep}}$, i.e. $\hat{\sigma}=\mathrm{Tr}_2\big[\hat{U}_{1/2}\,\hat{\rho}_{\mathrm{sep}}\,\hat{U}^{\dagger}_{1/2}\big]$.” The following paragraph specifies the tensor product of two pure states and the notation $\hat{\sigma}(\psi,\varphi)$.
- Page 4, Definition 2 (Extreme point): “Given a convex set $\mathcal{C}$, the point $a\in\mathcal{C}$ is an extreme point of $\mathcal{C}$ if and only if $\forall x,y\in\mathcal{C}:a=\frac12(x+y)\Leftrightarrow x=y=a$.”
- Page 3, Section 2, Preliminaries: “We denote by $\mathcal{D}\subset\mathcal{B}_1$ the set of Hermitian positive semi-definite (PSD) operators of unit trace and refer to operators in $\mathcal{D}$ as states.” The introduction on page 1 calls the set $\mathcal{D}_{+}$ of quantum states with non-negative Wigner function “Wigner-positive states (WPS)”.
- Page 6, Section 3.1, Bounded support quasi-states, equation (16): “Consider a quasi-state $\hat{A}\in\mathcal{A}^{n}$, with Fock matrix elements $A_{k\ell}=\bra{k}\hat{A}\ket{\ell}$. The Wigner function of $\hat{A}$ is here expressed as:” $W_{\hat A}(\alpha,\alpha^{\ast})=\sum_{k,\ell=0}^{n}A_{k\ell}W_{k\ell}(\alpha,\alpha^{\ast})$.
- Page 18, Appendix A.1 (Operator-sum representation), equation (48), source label `wigner_funcion_fock_mn`: $W_{|m\rangle\langle n|}(\alpha)=\frac{2}{\pi}(-1)^m\sqrt{m!/n!}(2\alpha)^{n-m}L_m^{(n-m)}(4|\alpha|^2)e^{-2|\alpha|^2}$ “for $m\leq n$, otherwise use the relation $W_{\ket{n}\bra{m}}=W^{\ast}_{\ket{m}\bra{n}}$.”
- Page 15, Section 6 (Conclusion and open problems): “This leads us to formulate the following open problem: for any two Fock-bounded pure states $\ket\psi,\ket\phi$ is the beamsplitter state $\hat\sigma(\psi,\phi)$ an extreme WPS?”

## Finite-matrix interpretation

Fock cutoff $K$ uses $(K+1)\times(K+1)$ complex matrices, with positive
semidefiniteness, unit trace and pointwise non-negative Wigner function.
The generalized Laguerre polynomial uses the explicit finite sum
$L_m^{(k)}(x)=\sum_{i=0}^{m}(-1)^i\binom{m+k}{m-i}x^i/i!$.

The repository beam splitter rotates coherent amplitudes as
$(t\alpha-r\beta,r\alpha+t\beta)$; the paper uses
$(t\alpha+r\beta,-r\alpha+t\beta)$. Conjugating by second-mode parity relates
the two. Output parity vanishes under the partial trace; input parity permutes
the finite-Fock pure states and fixes the even-supported inputs
$(|0\rangle\pm a|2\rangle)/\sqrt{1+a^2}$.
These conventions are fixed in issue
[14447](https://github.com/the-omega-institute/trureturing/issues/14447).
A midpoint decomposition supported on levels zero through four is also a
midpoint decomposition in the full WPS set.

The paper proves extremality for two Fock-state inputs. Its Vertigo-map results
and its use of the companion Krein–Milman theorem do not assume a positive
answer to the quoted open problem.
