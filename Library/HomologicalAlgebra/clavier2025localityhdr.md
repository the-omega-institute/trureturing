---
bibkey: clavier2025localityhdr
authors: Pierre J. Clavier
year: 2025
title: "TRAPs, Generalisations of MZVs, Locality and Resurgence for Quantum Field Theories"
doi: null
url: https://arxiv.org/abs/2506.09493v1
claim: "The habilitation thesis surveys the locality framework for renormalisation and states as its Conjecture conj:loc_tensor that for any locality vector space (E,⊤) and any two locality subspaces V and W, the locality tensor product V⊗_⊤W with the quotient locality relation is a locality vector space."
strata_touched:
  - D5/S3/HomologicalAlgebra/LocalityTensorProductRefutation
license: citation-only
triage: anchor
---

# TRAPs, Generalisations of MZVs, Locality and Resurgence for Quantum Field Theories

P. J. Clavier, habilitation thesis (Université de Haute-Alsace), arXiv:2506.09493v1 [math-ph]. Quotations are from the v1 TeX source.

The quotient locality (Definition `defn:quotientlocality`):

> For a subspace $W$ of a  locality vector space $(V, \top)$, we call {\bf quotient locality} on the quotient $V/ W$, the final locality relation $\left([u]\ttop[v]~\Longleftrightarrow \exists(u',v')\in[u]\times[v]:~u'\top v'\right)$

The conjecture (Conjecture `conj:loc_tensor`), introduced as the most important open gap of the locality framework:

> Let $(E,\top)$ be any locality vector space, $V$ and $W$ any two locality vector subspaces of $E$. Then $(V\otimes_\top W,\ttop)$ is a locality vector space.

and, among the listed evidence:

> We could not find counterexamples, although we did spend time and effort to build them.

The locality cartesian power (Eq. `eq:lprod`):

> $X^{_\top k}: = \underbrace{X \times_\top \cdots \times_\top X}_{k \text{ factors}}: = \left\{ (x_1,\cdots,x_k)\in X^k\,\left|\, (x_i,x_j)\in \top, 1\leq i\neq j\leq k\right.\right\}.$

and the explicit description of the tensor locality:

> Then for $X, Y\in E\otimes_\top E$, we have $X\top_{\otimes 2} Y$ if we can write $X=\sum_i v_i\otimes w_i,\qquad Y=\sum_i v'_i\otimes w'_i$ such that $(v_i,w_i,v'_j,w'_j)\in E^{\times_\top 4}$ for any $i$ and $j$.

(the displays are written inline here).

## Verified locator

Source: https://arxiv.org/abs/2506.09493v1
- URL: https://arxiv.org/abs/2506.09493v1 (source chapter `LOC.tex`, md5 `41f5e772e40d5eaf8583e8903293dbbb`, 1831 lines):
  - the locality cartesian power, Eq. `eq:lprod`, l. 219–221;
  - the quotient locality, Definition `defn:quotientlocality`, l. 606–612;
  - the explicit description of the tensor locality through $E^{\times_\top4}$, l. 743–747;
  - the statement that $E\otimes_\top E$ being a locality vector space is still a conjecture, l. 749;
  - the conjecture and its evidence, Conjecture `conj:loc_tensor`, l. 1794–1806.
