---
bibkey: yaolisun2019coherencefraction
authors: Yao Yao; Dong Li; C. P. Sun
year: 2019
title: "Quantum coherence fraction"
doi: 10.1103/PhysRevA.100.032324
url: https://arxiv.org/abs/1906.09789v1
claim: "The paper introduces the quantum coherence fraction, the largest overlap of a density matrix with a maximally coherent state, studies its properties and its relation to the robustness of coherence and to genuinely incoherent operations, proves that it equals a modified robustness for qubit and qutrit states, and conjectures, by analogy with the fully entangled fraction, that it may not be monotone under general incoherent operations."
strata_touched:
  - D5/S3/Quantum/Measurement/CoherenceFractionIncoherentNonmonotone
license: citation-only
triage: anchor
---

# Yao, Li and Sun, the quantum coherence fraction

Y. Yao, D. Li and C. P. Sun, arXiv:1906.09789v1 [quant-ph] (24 June 2019); Phys. Rev. A 100, 032324 (2019). Quotations are from the v1 TeX source, with figure and theorem references replaced by bracketed descriptions.

Setting (Section II): density operators on $\mathbb C^d$ with the computational basis as incoherent basis; incoherent states are the diagonal ones, and

> Any incoherent operation admits a Kraus representation $\Phi(\rho)=\sum_iK_i\rho K_i^\dagger$ such that every Kraus operator is required to fulfill $K_i\rho K_i^\dagger/\textrm{tr}(K_i\rho K_i^\dagger)\in\mathcal{I}$ for all $\rho\in\mathcal{I}$

The quantum coherence fraction is

> $C_{\mathcal{F}}(\rho)=\max_{|\phi\rangle\in\mathcal{MCS}}\langle\phi|\rho|\phi\rangle =\max_{U\in\mathcal{U}_d}\langle\phi^+|U^\dagger\rho U|\phi^+\rangle$,

with $|\phi^+\rangle=d^{-1/2}\sum_i|i\rangle$ and $\mathcal U_d$ the diagonal unitaries.

The conjecture (Section V):

> First, similar to the behavior of fully entangled fraction [Badziag et al. 2000], we conjecture that $C_{\mathcal{F}}(\rho)$ may not satisfy the monotonicity under general incoherent operations. However, in low-dimensional cases, it would be an exhausting work to search for an incoherent operation $\Phi$ such that $C_{\mathcal{F}}(\Phi(\rho))\geq C_{\mathcal{F}}(\rho)$ since from [Fig. 3] it is shown that $C_{\mathcal{F}}(\rho)$ is quite close to $\overline{C}_{\mathcal{R}}(\rho)$, which is a MIO monotone

## Verified locator

Source: https://arxiv.org/abs/1906.09789v1
- DOI: https://doi.org/10.1103/PhysRevA.100.032324 (Phys. Rev. A 100, 032324 (2019); author list, journal, volume and article number from Crossref).
- URL: https://arxiv.org/abs/1906.09789v1 (the e-print is a gzipped tar archive; member `CF.tex`, 654 lines, md5 `04c3da80687e28f16b7b2308e2173201`):
  - incoherent states and incoherent operations, l. 122–132;
  - the quantum coherence fraction, l. 141–151;
  - the conjecture, l. 422–425.
- The arXiv version date is from the arXiv metadata.
