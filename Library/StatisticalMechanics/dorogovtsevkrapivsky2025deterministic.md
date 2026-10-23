---
bibkey: dorogovtsevkrapivsky2025deterministic
authors: S. N. Dorogovtsev; P. L. Krapivsky
year: 2025
title: "Deterministic simplicial complexes"
doi: 10.1088/1742-5468/ae2092
url: https://arxiv.org/abs/2507.07402v1
claim: "The paper studies simplicial complexes that grow deterministically from one vertex, every existing simplex joining a new vertex at each step; it computes the numbers of simplices, the upper-degree distributions and Hodge Laplacian spectra, studies constrained versions with bounded dimension, and states several relations observed for early generations as conjectures, among them the relation K^(d)(n) = 0 ∪ K^(0)(n−d) between the sets of distinct upper degrees."
strata_touched:
  - D5/S3/StatisticalMechanics/DeterministicSimplicialDegreeShift
license: citation-only
triage: anchor
---

# Deterministic simplicial complexes

S. N. Dorogovtsev and P. L. Krapivsky, arXiv:2507.07402v1; J. Stat. Mech. (2025) 123404. Quotations are from the v1 TeX source.

The model:

> We investigate simplicial complexes deterministically growing from a single vertex. In the first step, a vertex and an edge connecting it to the primordial vertex are added. The resulting simplicial complex has a 1-dimensional simplex and two 0-dimensional faces (the vertices). The process continues recursively: On the $n$-th step, every existing $d-$dimensional simplex ($d\leq n-1$) joins a new vertex forming a $(d+1)-$dimensional simplex; all $2^{d+1}-2$ new faces are also added so that the resulting object remains a simplicial complex.

Upper degrees:

> the upper degree $k^{(d)}$ of a $d$-simplex is the number of $(d{+}1)$-simplices sharing this $d$-simplex as a face.

The relation between degree sets:

> Another useful general relation $K^{(d)}(n) = 0 \cup K^{(0)}(n-d)$ is conjecturally valid for all $n \geq d + 1$ and $d \geq 1$.

## Verified locator

Source: https://arxiv.org/abs/2507.07402v1
- URL: https://arxiv.org/abs/2507.07402v1 (source `DSC-7.tex`, md5 `49162ddd2644bf0933cad90accf4238f`):
  - the model, l. 82;
  - the primordial complex, l. 118;
  - upper degrees, l. 106;
  - the lists $K^{(d)}(n)$ for $n\le5$, l. 427–503;
  - the relation (34), l. 505–510.
- DOI: 10.1088/1742-5468/ae2092 (https://doi.org/10.1088/1742-5468/ae2092).
