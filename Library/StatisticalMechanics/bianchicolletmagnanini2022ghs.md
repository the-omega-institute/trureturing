---
bibkey: bianchicolletmagnanini2022ghs
authors: Alessandra Bianchi; Francesca Collet; Elena Magnanini
year: 2022
title: "The GHS and other correlation inequalities for the two-star model"
doi: 10.30757/ALEA.v19-64
url: https://arxiv.org/abs/2107.08889v2
claim: "The paper proves the FKG, GKS and GHS inequalities for the two-star exponential random graph model with nonnegative parameters, extends FKG and GKS to general exponential random graphs with nonnegative non-edge coefficients, and conjectures that in this general setting the GHS inequality holds exactly when every edge marginal is at least one half."
strata_touched:
  - D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation
license: citation-only
triage: anchor
---

# Bianchi, Collet and Magnanini, the GHS and other correlation inequalities for the two-star model

A. Bianchi, F. Collet and E. Magnanini, arXiv:2107.08889v2 [math.PR] (6 December 2021; v1 19 July 2021); ALEA Lat. Am. J. Probab. Math. Stat. 19 (2022) 1679–1695. Quotations are from the v2 TeX source, with the macros `\cG`, `\cE`, `\b`, `\E` written as $\mathcal G$, $\mathcal E$, $\beta$, $\mathbb E$ and cross-references omitted.

The homomorphism density, for $G\in\mathcal G_n$ and a finite simple graph $H$:

> $t(H,G) := \frac{|\text{hom}(H,G)|}{|V(G)|^{|V(H)|}}$,

and the exponential random graph with pre-chosen finite simple graphs $H_1,\dots,H_k$ and real parameters $\beta_1,\dots,\beta_k$:

> $\mu_{n; \boldsymbol{\beta}} (G)=\frac{\exp \left(H_{n,\boldsymbol{\beta}}(G)\right)} {Z_{n;\boldsymbol{\beta}}} \quad \mbox{for } G\in\mathcal G_n$, with $H_{n;\boldsymbol{\beta}}(G)=n^2\sum_{j=1}^{k}\beta_{j}t(H_{j},G)$.

The third Ursell function of the edge indicators $x_i$:

> $u_3(i,j,k) = \mathbb E( x_i x_j x_k ) - \mathbb E( x_i ) \, \mathbb E( x_j x_k ) - \mathbb E( x_j ) \, \mathbb E( x_i x_k ) - \mathbb E( x_k ) \, \mathbb E( x_i x_j ) + 2 \mathbb E( x_i ) \mathbb E( x_j ) \mathbb E( x_k )$,

and the GHS inequality: for all $i,j,k\in\mathcal E_n$, $u_3(i,j,k)\leq 0$.

The general setting (Section 4) takes $H_1$ to be an edge; for $\beta_1\in\mathbb R$ and $\beta_2,\dots,\beta_k\ge0$ the FKG lattice condition and the GKS inequality hold. The closing conjecture:

> Since $\text{Cov}_{n;\boldsymbol{\beta}}(x_i,x_j) \geq 0$, due to the GKS inequality, we can conjecture that the necessary and sufficient condition for the GHS inequality to hold in the present general setting is again only the requirement $\mathbb{E}_{n;\boldsymbol{\beta}}(x_i) \geq 1/2$.

## Verified locator

Source: https://arxiv.org/abs/2107.08889v2
- DOI: https://doi.org/10.30757/ALEA.v19-64 (ALEA 19 (2022) 1679–1695; author list, journal, volume and first page from Crossref).
- URL: https://arxiv.org/abs/2107.08889v2 (the e-print is a gzipped tar archive; member `GHS_arXiv-replacement.tex`, 1428 lines, md5 `b353bfa014348d3c29f4b9c509b5665d`):
  - the homomorphism density, the Gibbs density and the Hamiltonian, l. 286–312;
  - the edge set $\mathcal E_n$ and the edge indicators, l. 322–331;
  - the Ursell function $u_3$, l. 577–589;
  - the GHS inequality, Definition 3.4, l. 617–636;
  - the general setting, Lemma 4.1 and the GKS inequality, l. 1243–1287;
  - the conjecture, l. 1322.
- The author list and the arXiv dates are from the arXiv metadata.
