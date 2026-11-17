---
bibkey: lipoonsze2011realignment
authors: Chi-Kwong Li; Yiu-Tung Poon; Nung-Sing Sze
year: 2011
title: "A note on the realignment criterion"
doi: 10.1088/1751-8113/44/31/315304
url: https://arxiv.org/abs/1103.2499v2
claim: "The paper studies elementary symmetric functions of realignment singular values, gives explicit prescribed-spectrum density matrices, and asks whether the separable maximum is strictly smaller than the CCNR-admissible maximum."
strata_touched:
  - D5/S3/Quantum/Entanglement/Witness/RealignmentSchurBound
  - D5/S3/Quantum/Entanglement/Witness/LiPoonSzeP2
license: citation-only
triage: anchor
---

# Li, Poon and Sze, A note on the realignment criterion

C.-K. Li, Y.-T. Poon and N.-S. Sze, *Journal of Physics A: Mathematical
and Theoretical* 44 (2011), 315304.

## Locator

URL: https://arxiv.org/abs/1103.2499v2

DOI: 10.1088/1751-8113/44/31/315304

The definitions, quotations and construction formulas below are supplied
in the preregistered problem brief, issue #30506. They are not a fresh
retrieval of the paper.

## Elementary symmetric realignment functions

For $m\le n$, realignment sends
$\rho_{(i,a),(j,b)}$ to the matrix with entries
$R(\rho)_{(i,j),(a,b)}=\rho_{(i,a),(j,b)}$.
The paper's $f_\ell$ is the elementary symmetric function of its $m^2$
nonnegative singular values. Its question (P2) is

> To determine if $\widetilde B_\ell(m,n)>B_\ell(m,n)$.

Here $B_\ell$ maximizes over separable density matrices, while
$\widetilde B_\ell$ maximizes over density matrices satisfying the CCNR
constraint $\sum_i s_i\le1$. Section 4 gives equality at $m=n$ and
reports numerical evidence for strict inequality at unequal dimensions.
The separate question (P1) asks for exact extremal values.

## Density constructions

Write $n=mq+r$, $0\le r<m$. Theorem 2.3 uses
$F_{ij}=(E_{ij}\otimes I_q)\oplus0_r$ and

$$
\rho=t\sum_{i,j}E_{ij}\otimes F_{ij}
  +u I_m\otimes(I_{mq}\oplus0_r)
  +v I_m\otimes(0_{mq}\oplus I_r).
$$

For $\alpha=1/\sqrt{mn}$ and
$\beta=(1-\alpha)/(m^2-1)$, the parameters are
$t=\beta/\sqrt q$, $u=\alpha^2-\beta/(m\sqrt q)$,
$v=\alpha^2$. The stated positivity range is
$m\le n\le m^3-m/2$. The row Gram has eigenvalues
$\alpha^2$ once and $\beta^2$ with multiplicity $m^2-1$.

For $n\ge m^3$, the paper embeds the $q=m^2$ entangled block with
coefficient $1/m^3$ and zero complement. Its realignment singular values
are all $1/m^2$.

The supported interpolation at $q=m^2-1$, its scalar comparison with the
covariance threshold, and the combination with a covariance tail estimate
are repository derivations, rather than claims attributed to this paper.

## Relation to covariance and correlation minor bounds

The covariance estimate is prior work, as recorded in
[Peled, Te'eni, Carmi and Cohen](peledteenicarmicohen2021minor.md).
Their filter-normal-form bounds have additional hypotheses. The
rectangular comparison here uses the covariance tail budget for general
separable states; it does not assert an exact solution of (P1) or remove
the hypotheses of every correlation minor norm bound.
