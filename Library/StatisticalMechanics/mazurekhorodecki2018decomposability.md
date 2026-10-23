---
bibkey: mazurekhorodecki2018decomposability
authors: Paweł Mazurek; Michał Horodecki
year: 2018
title: "Decomposability and convex structure of thermal processes"
doi: 10.1088/1367-2630/aac057
url: https://arxiv.org/abs/1707.06869v2
claim: "Thermal processes on diagonal states are the column-stochastic matrices preserving the Gibbs vector; the paper describes their extreme points for three levels and conjectures that an extremal process that factors into extremal processes on proper subspaces and is not a direct sum cannot satisfy detailed balance."
strata_touched:
  - D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation
license: citation-only
triage: anchor
---

# Decomposability and convex structure of thermal processes

P. Mazurek and M. Horodecki, arXiv:1707.06869v2; New J. Phys. 20, 053040 (2018). Quotations are from the v2 TeX source.

Thermal processes as matrices:

> From above it is visible that every TP can be represented as a left stochastic (i.e., with elements summing to $1$ within each column), Gibbs preserving matrix $T$: $T\boldsymbol{g}=\boldsymbol{g}$, where $\boldsymbol{g}$: $g_{i}=q_{i,0}/\sum\limits_{j} q_{j,0}$. Without loss of generality here and in the whole paper we assume that the ground state energy of the system is zero: $E_{0}=0$.

Processes acting on fewer levels, in the proof that the star process is not decomposable:

> Now we show that $P$ cannot be decomposed as a composition of TPs, each acting on at most $d-1$ dimensional subspace. Every such decomposition would take a form $P=AB$, where both $A$ and $B$ are TPs.

The conjugation and detailed balance:

> It follows that $\tilde{A}_{i,j}=A_{j,i}^{T}e^{-\beta(E_{i}-E_{j})}$. It can be rewritten as $\tilde{A}=M_{\rho_{\beta}}A^{T}M_{\rho_{\beta}}^{-1}$, where $M_{\rho_{\beta}}=diag[1,q_{1,0},\dots,q_{d-1,0}]$ is a matrix storing on its diagonal values proportional to occupations in a Gibbs state.

> Self-duality with respect to such a scalar product ($\tilde{A}=A$) served as a definition of detailed balance for generator of dynamical semigroup

Conjecture 1:

> If an extremal TP $C$ for $d$ dimensional space is decomposable into a sequence of extremal TPs $A$, $B$, each acting non-trivially on at most $d-1$ dimensional space: $C=AB$, and $C$ is not a direct sum of extremal TPs from lower dimensional subspaces, then $C$ is not self-dual with respect to the conjugation associated with the operator scalar product.

## Verified locator

Source: https://arxiv.org/abs/1707.06869v2
- URL: https://arxiv.org/abs/1707.06869v2 (source `manuscript.tex`, md5 `69e7001dd049721e95968ea93ad550c2`):
  - thermal processes as Gibbs-preserving column-stochastic matrices, l. 159;
  - processes acting on fewer levels, l. 208–211;
  - the conjugation and self-duality, l. 417–418;
  - Conjecture 1, l. 425–427.
- DOI: 10.1088/1367-2630/aac057 (https://doi.org/10.1088/1367-2630/aac057).
