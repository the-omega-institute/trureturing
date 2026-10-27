---
bibkey: fullwoodmawu2026spatiotemporalborn
authors: James Fullwood; Zhihao Ma; Zhen Wu
year: 2026
title: "Quasiprobabilistic nature of the spatiotemporal Born rule"
doi: 10.1103/cw25-pqx1
url: https://arxiv.org/abs/2507.16919v2
claim: "The paper compares the Lüders-von Neumann distribution of two-point sequential measurements with the Terletsky-Margenau-Hill quasiprobability distribution, shows that a spatiotemporal Born rule exists for the Lüders-von Neumann distribution when the initial state is maximally mixed or the channel is discard-and-prepare, and asks whether one of these two conditions is also necessary in arbitrary dimension."
strata_touched:
  - D5/S3/Quantum/Measurements/SpatiotemporalBornRuleDichotomy
license: citation-only
triage: anchor
---

# Quasiprobabilistic nature of the spatiotemporal Born rule

J. Fullwood, Z. Ma and Z. Wu, arXiv:2507.16919v2 (10 January 2026; v1 22 July 2025), titled "The spatiotemporal Born rule is quasiprobabilistic"; Phys. Rev. A 113(3) (2026), 032204. Quotations are from the v2 TeX source, with the macros `\E`, `\A`, `\B`, `\H` written as $\mathcal E$, $\mathcal A$, $\mathcal B$, $\mathcal H$ and `\define` as plain text.

Channels and projective measurements:

> A linear map $\mathcal E:\mathcal A\to \mathcal B$ which is completely positive and trace-preserving (CPTP) will be referred to as a quantum channel. … A collection of operators $\{P_i\}$ on a finite-dimensional Hilbert space $\mathcal H$ is said to be a projective measurement if and only if $P_iP_j=\delta_{ij}P_i$ and $\sum_iP_i=\mathds{1}$.

The Lüders-von Neumann distribution of a two-point sequential measurement $(\rho,\{P_i\},\mathcal E,\{Q_j\})$ is $\mathbf P(i,j)=\operatorname{Tr}[\mathcal E(P_i\rho P_i)Q_j]$.

The spatiotemporal Born rule:

> A spatiotemporal Born rule is then said to exist for the LvN distribution with respect to the pair $(\mathcal E,\rho)$ if and only if there exists an operator $\varrho_{AB}$ such that for all TPSM scenarios $(\rho,\{P_i\},\mathcal E,\{Q_j\})$, $\operatorname{Tr}[\varrho_{AB}(P_i\otimes Q_j)]=\mathbf{P}(i,j)\equiv \operatorname{Tr}[\mathcal E(P_i \rho P_i) Q_j]$.

The open question:

> It is then natural to ask whether $\rho$ being maximally mixed or $\mathcal E$ being a discard-and-prepare channel is also a necessary condition for the existence of the spatiotemporal Born rule for the LvN distribution. While it is straightforward to show that this is indeed the case when $A$ consists of a single qubit, for systems of arbitrary dimension we leave it as an open question.

A discard-and-prepare channel is $\mathcal E(a)=\operatorname{Tr}[a]\sigma$ for a state $\sigma$ (Proposition 1).

## Verified locator

Source: https://arxiv.org/abs/2507.16919v2
- URL: https://arxiv.org/abs/2507.16919v2 (the e-print is a tar archive; member `PRA_rev.tex`, 623 lines, md5 `ccc824023e2958b612ebb8c2be819e2f`):
  - channels and projective measurements, l. 231;
  - the Lüders-von Neumann distribution, l. 247–250;
  - discard-and-prepare channels, Proposition 1, l. 271;
  - the spatiotemporal Born rule, l. 534–537;
  - the open question, l. 577.
- DOI: 10.1103/cw25-pqx1 (https://doi.org/10.1103/cw25-pqx1; Crossref lists Physical Review A, volume 113, issue 3, article 032204, published 5 March 2026).
