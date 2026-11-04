---
bibkey: strattonhsiehskrzypczyk2026concentration
authors: Benjamin Stratton; Chung-Yun Hsieh; Paul Skrzypczyk
year: 2026
title: "Unspeakable coherence concentration"
doi: 10.1103/fj8w-v1bb
url: https://arxiv.org/abs/2512.04255v1
claim: "The paper studies the concentration of unspeakable coherence, measured mode by mode with respect to a truncated number operator, from two identical copies of a state into one by allowed unitaries that commute with the total number operator; it characterises the qubit case completely, gives upper bounds beyond qubits, constructs a qubit concatenation protocol, exhibits a family of qubit states with bound coherence, and leaves open whether bound-coherent states exist in higher dimensions."
strata_touched:
  - D5/S3/Quantum/Measurement/BoundCoherenceHigherDimensions
license: citation-only
triage: anchor
---

# Stratton, Hsieh and Skrzypczyk, unspeakable coherence concentration

B. Stratton, C.-Y. Hsieh and P. Skrzypczyk, arXiv:2512.04255v1 [quant-ph] (3 December 2025); Phys. Rev. A 113, 062429 (2026). Quotations are from the v1 TeX source, with macros expanded.

Coherence and allowed unitaries (Section II): a state is coherent with respect to a Hermitian observable $L$ if and only if $[\rho,L]\neq0$; on a bipartite system $L_{AB}=L_A\otimes\mathbb I_B+\mathbb I_A\otimes L_B$, allowed unitaries commute with $L_{AB}$, and the local observables are the truncated number operators $L_X=\sum_{n=0}^{d-1}n|n\rangle\langle n|_X$.

Modes and the figure of merit (Sections III–IV):

> $\rho^{(j)} \coloneqq \sum_{n=0}^{d-1}|n+j\rangle\langle n+j| \rho |n\rangle\langle n|$,

$M^{(j)}(\rho)=\|\rho^{(j)}\|_1$ with $\|P\|_1=\operatorname{tr}\sqrt{PP^\dagger}$, and

> $\Delta M^{(j)}_A \coloneqq \max_{V_{AB}}  M^{(j)}(\sigma_A)- M^{(j)}(\rho_A)$,

over all allowed unitaries $V_{AB}$, where $\sigma_A=\operatorname{tr}_B[V_{AB}(\rho_A\otimes\rho_B)V_{AB}^\dagger]$.

The question (Section IX):

> Finally, a family of states with bound-coherence was shown to exist, i.e., states that are not maximally coherent, nor incoherent, but for which no allowed unitary exists to perform coherence concentration. We leave it open to determine if such states exist in higher dimensions.

## Verified locator

Source: https://arxiv.org/abs/2512.04255v1
- DOI: https://doi.org/10.1103/fj8w-v1bb (Phys. Rev. A 113, 062429 (2026); author list, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2512.04255v1 (the e-print is a gzipped tar archive; member `main.tex`, 1476 lines, md5 `0a7beea9e160c8ab91648f9c5be643bd`):
  - coherence with respect to $L$, l. 211;
  - the bipartite observable and allowed unitaries, l. 221;
  - the truncated number operators, l. 224;
  - modes, l. 230–232;
  - the local-mode lemma, l. 245–252;
  - $M^{(j)}$ and $\Delta M^{(j)}_A$, l. 260–265;
  - the question, l. 387.
- The arXiv version date is from the arXiv metadata.
