---
bibkey: czartowskideoliveirajuniorkorzekwa2023thermalrecall
authors: Jakub Czartowski; A. de Oliveira Junior; Kamil Korzekwa
year: 2023
title: "Thermal Recall: Memory-Assisted Markovian Thermal Processes"
doi: 10.1103/PRXQuantum.4.040304
url: https://arxiv.org/abs/2303.12840v2
claim: "Markovian thermal processes on a system extended by an N-dimensional memory in its thermal state approximate thermal operations, through protocols built from two-level thermalisations with a memory reset after each transposition. At infinite temperature the paper conjectures, from numerics, that omitting the intermediate memory resets never worsens the total variation distance to the target permutation of the state."
strata_touched:
  - D5/S3/StatisticalMechanics/ThermalRecallTruncationRefutation
license: citation-only
triage: anchor
---

# Czartowski, de Oliveira Junior and Korzekwa, Thermal Recall

J. Czartowski, A. de Oliveira Junior and K. Korzekwa, PRX Quantum 4, 040304 (2023); arXiv:2303.12840v2. Quotations are from the v2 TeX source, with the source's macros `\v` (bold vectors), `\T` and `\P` (calligraphic letters) and `\qty` expanded.

A two-level thermalisation $T_{ij}$ (Definition 3) replaces $p_i,p_j$ by $\frac{p_i+p_j}{\gamma_i+\gamma_j}\gamma_i$ and $\frac{p_i+p_j}{\gamma_i+\gamma_j}\gamma_j$; at $\beta=0$ it averages the two entries and the memory state $\boldsymbol\eta_M$ is uniform. The protocol for a transposition of levels $i$ and $j$ of a $d$-level system with an $N$-dimensional memory consists of rounds

> $$\mathcal{R}^{(ij)}_k(\mathbf p \otimes \boldsymbol\gamma_M) := \Big(\prod_{l=1}^N T_{(i-1)N + k,\,(j-1)N + l}\Big) (\mathbf p \otimes \boldsymbol\gamma_M),$$

$\widetilde{\mathcal P}^{(ij)}=\mathcal R^{(ij)}_N\circ\cdots\circ\mathcal R^{(ij)}_1$, followed by the memory reset $\mathcal T(\mathbf Q)=\mathbf q\otimes\boldsymbol\gamma_M$, $q_i=\sum_jQ_{N(i-1)+j}$, giving $\mathcal P^{(ij)}=\mathcal T\circ\widetilde{\mathcal P}^{(ij)}$. For a decomposition $\Pi=\Pi_{i_mj_m}\cdots\Pi_{i_1j_1}$ into neighbour transpositions, $\mathcal P^{\Pi}$ composes the $\mathcal P^{(i_kj_k)}$ and $\widetilde{\mathcal P}^{\Pi}=\mathcal T\circ\widetilde{\mathcal P}^{(i_mj_m)}\circ\cdots\circ\widetilde{\mathcal P}^{(i_1j_1)}$. Distances are total variation, $\delta(\mathbf p,\mathbf q)=\tfrac12\sum_i|p_i-q_i|$.

> **Conjecture 1** (Improved convergence). In the infinite temperature limit, $\beta=0$, and for an $N$-dimensional memory, $\widetilde{\mathcal{P}}^{\Pi}$ gives a better approximation of a permutation $\Pi$ than $\mathcal{P}^{\Pi}$: $\delta(\Pi \mathbf p,\tilde{\mathbf q}) \leq \delta(\Pi \mathbf p, \mathbf q)$, where $\tilde{\mathbf q}$ and $\mathbf q$ are defined via $\widetilde{\mathcal{P}}^{\Pi}(\mathbf p\otimes \boldsymbol\eta_M) = \tilde{\mathbf q}\otimes \boldsymbol\eta_M$ and $\mathcal{P}^{\Pi}(\mathbf p\otimes \boldsymbol\eta_M) = \mathbf q\otimes \boldsymbol\eta_M$.

The text after the conjecture reports numerical evidence and states that for $\beta$-$k$-cycles there is no advantage to removing the intermediate thermalisations.

## Verified locator

Source: https://arxiv.org/abs/2303.12840v2
- DOI: https://doi.org/10.1103/PRXQuantum.4.040304 (PRX Quantum 4(4), article 040304; published 6 October 2023; title, authors, journal, volume, issue and article number from Crossref).
- URL: https://arxiv.org/abs/2303.12840v2. The e-print member `TR.tex` has 1370 lines and md5 `afa8fef9af0d09c95b9402cbc4e981d1`. Locations:
  - total variation, l. 235–239; two-level thermalisations, l. 269–275;
  - rounds and the truncated protocol, l. 289–296; the reset, l. 305–312; composite protocols, l. 315–324;
  - Conjecture 1, l. 417–427; the numerical remarks, l. 428.
