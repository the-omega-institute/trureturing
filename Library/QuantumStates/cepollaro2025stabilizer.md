---
bibkey: cepollaro2025stabilizer
authors: S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma, S. Lloyd
year: 2025
title: "Stabilizer Entropy of Subspaces"
doi: 10.48550/arXiv.2512.23013
url: https://arxiv.org/abs/2512.23013v1
claim: "Numerically, when the single-qudit dimension d_B is a power of 2, a three-dimensional subspace with zero average stabilizer entropy gap is always achievable; the authors state that it is unclear why."
strata_touched:
  - D5/S3/Quantum/Magic/CepollaroPowerOfTwoZeroMagicGap
license: citation-only
triage: anchor
---

# Cepollaro, Cuffaro, Weiss, Cusumano, Hamma and Lloyd, stabilizer entropy of subspaces

S. Cepollaro, G. Cuffaro, M. B. Weiss, S. Cusumano, A. Hamma and S. Lloyd, *Stabilizer
Entropy of Subspaces*, arXiv:2512.23013v1 (28 December 2025, quant-ph).

## Verified locator

DOI: 10.48550/arXiv.2512.23013.
Primary version: https://arxiv.org/abs/2512.23013v1 (the only arXiv version).
The TeX source `subspaceSRE_arxiv.tex` of v1 supplies §II (Weyl–Heisenberg group and linear
stabilizer entropy), §III (the average stabilizer entropy gap and its closed form), §V.A and
the Conclusion.

## Source statements

Weyl–Heisenberg group (§II.A): "$Z\ket{k}\equiv\omega^k\ket{k}$, $X\ket{k}\equiv\ket{k+1 \text{ mod } d}$,
where $\omega=e^{2\pi i /d}$", and "$D_\textbf{a}\equiv \tau^{a_1 a_2}X^{a_1}Z^{a_2}$, where
$\tau=-e^{i\pi/d}$".

Linear stabilizer entropy (§II.C): "$M(\psi)\equiv M_{\lin}^{(2)}(\psi)=1-\frac{1}{d^{n}}\sum_{\B{a}}|\trace(D_{\B{a}}^\dagger \psi)|^4=1-d^n\trace\left(Q\,\psi^{\otimes4}\right)$",
where "$Q_\alpha=\frac{1}{(d^{n})^\alpha}\sum_\textbf{a}(D_{\textbf{a}}\otimes D_{\textbf{a}}^\dagger)^{\otimes\alpha}$" and $Q\equiv Q_2$;
on one qudit (§III) "$Q_S = \frac{1}{d_S^2}\sum_\textbf{a}(D^S_{\textbf{a}}\otimes D_{\textbf{a}}^{S\dagger})^{\otimes2}$".

Average stabilizer entropy gap (§III): "$\Delta M(\mathcal{E}) \equiv \mathbb{E}_{\psi}\big[\Delta M(\psi)\big] = d_S\trace\left(Q_S \mathcal{A}^S_4\right)-d_B\trace\left(Q_B \mathcal{E}^{\otimes 4}(\mathcal{A}^S_4)\right)$",
with "$\mathcal{A}_4^S =\mathbb{E}_U\big[(U\psi U^\dagger)^{\otimes 4}\big]= \binom{d_S+3}{4}^{-1}\Pi^S_{\text{sym}^4}$" and
"$\Pi^S_{\text{sym}^4} = \frac{1}{24}\sum_{\sigma\in S_4} T_{\sigma}$", and the intrinsic average
"$1-\frac3{d_S+2}$" for odd $d_S$.

§V.A: "But this is not the only case: evidently, when $d_B$ is a power of 2, a zero ASE subspace
of dimension three is always achievable."

Conclusion: "It is unclear why, in the single-qudit case, when the global Hilbert space has
dimension a power of two, zero magic gap subspaces of dimension three consistently emerge."

## Scope

The observation comes from numerical optimization over three-dimensional subspaces for
$d_B=3,\dots,16$. The paper proves zero or negative gap for stabilizer codespaces (its Theorem 2);
a three-dimensional subspace of $\mathbb C^{2^m}$ is not such a codespace.
