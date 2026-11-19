---
bibkey: gaoli2020sandpileidentity
authors: Yibo Gao, Rupert Li
year: 2021
title: "Compatible recurrent identities of the sandpile group and maximal stable configurations"
doi: 10.1016/j.dam.2020.08.028
url: https://arxiv.org/abs/2008.10079v1
claim: "The paper studies graphs whose recurrent identities for different sinks are compatible and graphs whose maximal stable configuration is the recurrent identity, proves this complete maximal identity property for several families including K_4 □ P_2, and conjectures, after computations for 1 < i, j <= 50, that K_4 □ P_2 is the only Cartesian product K_i □ P_j with the property."
strata_touched:
  - D5/S3/StatisticalMechanics/SandpileCompleteMaximalIdentity
license: citation-only
triage: anchor
---

# Gao and Li, compatible recurrent identities of the sandpile group

## Verified locator

DOI: https://doi.org/10.1016/j.dam.2020.08.028 (Discrete Appl. Math. 288, 123–137, 2021).

Source: https://arxiv.org/abs/2008.10079v1

Y. Gao and R. Li, arXiv:2008.10079v1. Quotations are from the v1 TeX source (`Paper/Conjectures.tex`).

## Statement

In the abelian sandpile model on a graph $G$ with sink $s$, the maximal stable configuration $m_G$ has $\deg v-1$ chips at every vertex $v$. $G$ has the maximal identity property at $s$ if $m_G$ is the recurrent identity for the sink $s$, and the complete maximal identity property if this holds for every vertex. After computations for $1<i,j\le50$ the source states:

> For $i,j \in \mathbb{Z}_{>1}$, the only graph $K_i \cp P_j$ which has the complete maximal identity property is $K_4 \cp P_2$.

with $\cp$ the Cartesian product, and proves the cases $j=2$ and $j=3$.

## Encoding and boundary

The candidate source states the property at a sink as membership of $m_G$ in the image of the integer reduced Laplacian (the maximal stable configuration is recurrent, and each class contains exactly one recurrent configuration), and contains a proof term asserting for all $i,j\ge2$ that every sink of $K_i\square P_j$ has the property exactly when $(i,j)=(4,2)$: a difference of firing values across two clique coordinates satisfies a tridiagonal system along the path whose corner cofactor is $1$, so integrality forces a continuant to divide $ij-2$. The companion conjecture for the strong product $P_i\boxtimes P_j$ (Conjecture 6.2 of the source) and recurrence theory itself are outside this conclusion.

Current-base compilation and admission of this candidate remain unverified. The bounded literature search reported in [#26439](https://github.com/the-omega-institute/trureturing/issues/26439) does not establish exhaustive novelty, priority, or the absence of other versions or later solutions. The recurrent-identity interpretation uses the source literature and is not a Lean theorem of this module.
