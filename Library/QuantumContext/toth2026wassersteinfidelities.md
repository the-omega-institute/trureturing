---
bibkey: toth2026wassersteinfidelities
authors: Géza Tóth; József Pitrik
year: 2026
title: "Quantum Wasserstein distance and its relation to several types of fidelities"
doi: null
url: https://arxiv.org/abs/2506.14523v6
claim: "For Hermitian observables H_1,...,H_N, the paper compares the De Palma-Trevisan quantum Wasserstein distance with its variant optimized over separable couplings, and conjectures (Conjecture 1) that the modified separable distance never exceeds the modified De Palma-Trevisan distance for arbitrary mixed states."
strata_touched:
  - D5/S3/Quantum/Information/SeparableWassersteinComparisonRefutation
  - D5/S3/Quantum/QuantumChannels/SeparableDecompositionTriangleRefutation
license: citation-only
triage: anchor
---

# Quantum Wasserstein distance and its relation to several types of fidelities

Géza Tóth and József Pitrik, arXiv:2506.14523v6 (quant-ph), 2026-02-12. Quotations are from the v6 TeX source.

The De Palma–Trevisan distance (Section II):

> One of the definitions of the quantum Wasserstein distance has been given by De Palma and Trevisan as \cite{DePalma2021Quantum}
> \begin{align}
> \begin{split}
> D_{\rm DPT}(\varrho,\sigma)^2\quad\\=\frac 1 2
> \min_{ \varrho_{12}}\sum_{n=1}^N\;&
> \trace[(H_n^T\otimes \openone-\openone\otimes H_n)^2  \varrho_{12} ],\\
> \textrm{s.~t. }&
> \varrho_{12}\in\mathcal D,\label{eq:DPT}  \\
> & {\rm Tr}_1(\varrho_{12})=\varrho^T, \\
> & {\rm Tr}_2(\varrho_{12})=\sigma,
> \end{split}

The modified distance:

> \begin{split}
> \tilde{D}_{\rm DPT}(\varrho,\sigma)^2&=D_{\rm DPT}(\varrho,\sigma)^2\\
> &-[D_{\rm DPT}(\varrho,\varrho)^2+D_{\rm DPT}(\sigma,\sigma)^2]/2.\label{eq:Dmod}
> \end{split}
> \end{align}

The separable distance (Section III):

> \begin{split}
> D_{\rm DPT, sep}(\varrho,\sigma)^2\quad\\=\frac 1 2
> \min_{ \varrho_{12}\in\mathcal D}\sum_{n=1}^N\;&
> \trace[(H_n\otimes \openone-\openone\otimes H_n)^2  \varrho_{12} ],\\
> \textrm{s.~t. }&
> \varrho_{12}\in\mathrm{Sep},\label{eq:GMPC_distance_sep}  \\
> & {\rm Tr}_1(\varrho_{12})=\varrho, \\
> & {\rm Tr}_2(\varrho_{12})=\sigma,
> \end{split}
> \end{align}

Its modified form:

> Following the idea for the definition of the modified quantum Wasserstein distance in \EQ{eq:Dmod}, let us now define an analogous quantity for the
> quantum Wasserstein distance  $D_{\rm DPT, sep}(\varrho,\sigma)$ as
> \begin{align}
> \begin{split}
> &\tilde D_{\rm DPT, sep}(\varrho,\sigma)^2=D_{\rm DPT, sep}(\varrho,\sigma)^2\\
> &\quad-[D_{\rm DPT,sep}(\varrho,\varrho)^2+D_{\rm DPT, sep}(\sigma,\sigma)^2]/2.\label{eq:tildeDPTsep}
> \end{split}

Conjecture 1:

> {\bf Conjecture 1.} The following inequality seems to hold
> \begin{align}
> \tilde D_{\rm DPT, sep}(\varrho,\sigma)^2  \le \tilde D_{\rm DPT}(\varrho,\sigma)^2\label{eq:DPTsepDPTConj}
> \end{align}
> if $\varrho$ and $\sigma$ are arbitrary mixed states.

## Pure-state decompositions and the triangle question

Equations (18) and (19) use a common finite probability distribution for two pure-state ensembles:

$$
\varrho_{12}=\sum_k p_k |\Psi_k\rangle\langle\Psi_k|\otimes|\Phi_k\rangle\langle\Phi_k|,
\qquad
\varrho=\sum_k p_k |\Psi_k\rangle\langle\Psi_k|,
\qquad
\sigma=\sum_k p_k |\Phi_k\rangle\langle\Phi_k|.
$$

Equation (83) defines the modified decomposition quantity:

$$
\widetilde D_{\mathrm{DPT,decomp}}(\varrho,\sigma)^2
=\min_{p_k,|\Psi_k\rangle,|\Phi_k\rangle}
\sum_k p_k\widetilde D_{\mathrm{DPT}}(|\Psi_k\rangle,|\Phi_k\rangle)^2.
$$

Section III.3.3 states:

> it would be important to show that these quantities fulfill the triangle inequality. Let us now examine this in the case of D̃_DPT,decomp(ϱ,σ).

Theorem 10, equation (114), states:

> The inequality D̃_DPT,decomp(ϱ,ω) + D̃_DPT,decomp(ω,τ) − D̃_DPT,decomp(ϱ,τ) ≥ 0, where ϱ, ω and τ are density matrices, is fulfilled for the case of a pure ω.

The formulas and the two quotations in this section use the supplied transcription of the same v6 source. The general mixed-middle-state triangle assertion is the question, whereas Theorem 10 has the additional pure-middle-state hypothesis.

## Verified locator

- URL: https://arxiv.org/abs/2506.14523v6 (v6, 2026-02-12; source `swap_fidelity_and_separability61.tex`, md5 `cf228e87bcfd90de27e7425f05127d95`): the De Palma–Trevisan distance (l. 151–161), its modification (l. 228–232), the separable distance (l. 246–255) and its modification (l. 797–803), and Conjecture 1 (l. 866–870).
- In the v6 transcription, equations (18) and (19) specify the common-weight pure-state ensembles and their two marginals; equation (83) defines the modified decomposition minimum; Section III.3.3 poses its triangle question; Theorem 10, equation (114), proves the pure-middle-state case. The formulas and quotations under "Pure-state decompositions and the triangle question" are located by these equation, section and theorem numbers.
