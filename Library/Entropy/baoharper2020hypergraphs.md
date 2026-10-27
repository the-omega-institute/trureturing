---
bibkey: baoharper2020hypergraphs
authors: Ning Bao; Jonathan Harper
year: 2020
title: "Bit threads on hypergraphs"
doi: 10.48550/arXiv.2012.07872
url: https://arxiv.org/abs/2012.07872v1
claim: "The paper extends bit threads and multiflows from graphs to hypergraph geometries. It defines the subflow of a union of boundary regions from the thread numbers of a multiflow, shows that a max multiflow saturates every single-region entropy, and conjectures that a linear combination of entropies that is nonnegative and somewhere nonzero on subflows equals its subflow value on every max multiflow. It names the Ingleton combination as satisfying these hypotheses."
strata_touched:
  - D5/S3/Entropy/BitThreadIngletonMultiflowRefutation
license: citation-only
triage: anchor
---

# Bao and Harper, bit threads on hypergraphs

N. Bao and J. Harper, arXiv:2012.07872v1 [hep-th], report number BRX-TH-6671. Quotations are from the v1 TeX source.

Subflows (Definition 1): for a multiflow with thread numbers $N_{ij}$ between boundary regions $A_i$ and $A_j$, the subflow of a union $B$ of boundary regions is $V_B=\sum_{A_i\in B,\,A_j\notin B}N_{ij}$. A max multiflow saturates every single-region entropy, $S(A_i)=V_{A_i}$ (Theorem 1), while in general the subflows of higher-party regions are not maximal.

For a linear combination $R(S)=\sum\alpha_IS_I-\sum\alpha_JS_J$ with $\alpha\ge0$, and $R(V)$ the same combination of subflows, Conjecture 1 reads:

> For a given geometry consider a linear combination of entropies $R(S)$. If $R(V)\geq0$ for all multiflows and there exists a multiflow such that $R(V)\neq0$, then for all max multiflows $R(S)=R(V)$.

The paper then notes that the Ingleton combination satisfies the hypotheses: "Ing(V) ≥ 0 and can easily be made non-zero". The geometries include 2-graphs, with entropies given by min-cuts.

## Verified locator

Source: https://arxiv.org/abs/2012.07872v1
- DOI: https://doi.org/10.48550/arXiv.2012.07872 (the arXiv-issued DataCite DOI; title and authors from the DataCite record).
- URL: https://arxiv.org/abs/2012.07872v1. The e-print is a gzipped tar archive; its member `BT_Hyper.tex` has 462 lines and md5 `e001e89a911f72e1614de54e82230780`. Locations:
  - multiflows and Definition 1, l. 95–115;
  - Theorem 1, l. 117–124;
  - the definition of $R$, l. 409–416, and the 2-graph footnote, l. 417;
  - Conjecture 1, l. 419–424, and the Ingleton remark, l. 426.
- Authors, title and date (14 December 2020) are from the arXiv metadata. The arXiv record lists no journal reference, and a Crossref title search returned no published version.
