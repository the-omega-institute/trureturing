---
bibkey: vegacoso2026spectraldualityrigidity
authors: Juan Antonio Vega Coso
year: 2026
title: "Axioms and internal rigidity of spectral duality structures"
doi: 10.48550/arXiv.2610.16454
url: https://arxiv.org/abs/2610.16454v1
claim: "Proposition 4.16 proves generic global uniqueness of insensitive distributions for N > m; Section 9 explicitly leaves the case N ≤ m open."
strata_touched:
  - D5/S3/ContinuousObservables/SpectralDualityUniquenessRefutation
license: citation-only
triage: anchor
---

# Axioms and internal rigidity of spectral duality structures

The source is arXiv:2610.16454v1. Proposition 4.16 is on page 11; its open extension question is in Section 9, page 18.

> In the setting of Proposition 4.15, assume moreover $N>m$ and (H1). Then there is an open dense subset $\mathcal G\subset\mathcal D$, whose complement has Lebesgue measure zero, such that for every $D\in\mathcal G$ for which $(A,\,B=\beta A+D)$ satisfies (H2), the distribution $\pi$ is the *only* insensitive distribution of $(A,B)$, at any level.

> Likewise, Proposition 4.16 is proved for $N>m$, and the case $N\le m$ is open.

The second quotation poses a question; it does not assert the extension. The refutation concerns the universal extension to $N\le m$, including $N=m=2$. It does not refute the published $N>m$ proposition.

The analytic setting on page 4 uses spectral functions $f_1,\ldots,f_N:(0,1)\to\mathbb R$, with

$$u_z(\gamma)=\sum_\nu f_\nu(\gamma)A_\nu(z),\qquad s_z(\gamma)=\sum_\nu f_\nu(\gamma)[A_\nu(z)+B_\nu(z)].$$

The coupling functional is $C(\pi,\gamma)=\langle\pi,u(\gamma)\rangle/\langle\pi,s(\gamma)\rangle$, where $\langle\pi,x\rangle=\sum_z\pi_zx_z$. Hypothesis (H1) is linear independence of the functions on $(0,1)$; (H2) is $s_z(\gamma)>0$ for every $z$ and every $\gamma$.

Definition 2.2, page 5:

> A distribution $\pi\in\overline\Delta$ is *insensitive at level $c$* if $C(\pi,\gamma)=c$ for every $\gamma\in(0,1)$.

The closed simplex consists of nonnegative vectors summing to one; its interior consists of strictly positive vectors summing to one. The proof of Proposition 4.16 identifies $\mathcal D=\{D:D\pi=0\}$, with its relative finite-dimensional topology.

The exact rational experiment is in `the-omega-institute/trureturing-experiments`, commit `1b1b992af693545024317f083d815cb170d39f79`, path `docs/reports/arxiv2610.16454-sec9-n_le_m-generic-global-uniqueness/check.py`, SHA-256 `988a571a3dfdabf15ed61422080e0b4e12e668b3ac4f16616e43f306a164a95c`. Its recorded exit code is 0 and its final line is `ALL_CHECKS_OK`. The experiment supports exact symbolic identities and the rational witness; the Lean result supplies the formal refutation.

The bounded literature screen is recorded in issue [#26267](https://github.com/the-omega-institute/trureturing/issues/26267). Exhaustive absence of an earlier published settlement is `ASSUMED-UNVERIFIED`.

## Verified locator

DOI: 10.48550/arXiv.2610.16454

Source: https://arxiv.org/abs/2610.16454v1

PDF: https://arxiv.org/pdf/2610.16454v1 — analytic setting page 4, Definition 2.2 page 5, Proposition 4.16 page 11, Section 9 page 18.
