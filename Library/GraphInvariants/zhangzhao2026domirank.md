---
bibkey: zhangzhao2026domirank
authors: Yingying Zhang and Chengye Zhao
year: 2026
title: "Theoretical Analysis of DomiRank Centrality: Automorphism, Entropy, and Graph Transformations"
doi: 10.48550/arXiv.2610.00107
url: https://arxiv.org/abs/2610.00107v1
claim: "the DomiRank entropy of a connected non-regular graph decreases monotonically with σ"
strata_touched:
  - D5/S3/Combinatorics/Graph/DomiRankEntropyRefutation
license: citation-only
triage: anchor
---

# DomiRank entropy and competition

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2610.00107
- Version: https://arxiv.org/abs/2610.00107v1
- Primary text: https://arxiv.org/html/2610.00107v1
- Target: Section 4.1, Remark 4.6.

Remark 4.6 states:

> This contrast indicates that the conditions of Theorem 4.5 are
> conservative, and the unconditional version — “the DomiRank entropy
> of a connected non-regular graph decreases monotonically with σ” —
> deserves further study as an open problem.

For a finite unweighted undirected simple graph with adjacency matrix
$A$, degree vector $d=A\mathbf1$, and competition parameter $\sigma$,
the source equilibrium with $\theta=1$ is

$$
\Gamma(\sigma)=\sigma(I+\sigma A)^{-1}d,
\qquad 0<\sigma<-1/\lambda_{\min}(A).
$$

The entropy uses the positive part of the scores and normalization:

$$
P_i(\sigma)=\frac{\max(\Gamma_i(\sigma),0)}
 {\sum_j\max(\Gamma_j(\sigma),0)},
\qquad H(\sigma)=-\sum_i P_i(\sigma)\log_2 P_i(\sigma).
$$

The source's graph product replaces each vertex by $m$ independent
clones and each edge by all edges between its two clone classes.
This is the graph on $V\times\operatorname{Fin}(m)$ whose adjacency
depends only on the original vertices. The entropy shift is
$H_{G_m}(s)=H_G(ms)+\log_2m$.

Theorem 4.5 supplies conditional sufficient criteria for entropy
decrease. Remark 4.6 asks whether those criteria can be removed;
the unconditional assertion is the target here. Conjecture 4.7, that
stars minimize DomiRank entropy among connected graphs, is a separate
question and is excluded.

## Literature boundary

The source identifier/version is retained exactly. Its displayed
submission date disagrees with the October arXiv identifier; no
chronology is inferred from that display. The bounded qualification
reported in preregistration [#13267](https://github.com/the-omega-institute/trureturing/issues/13267)
found no settlement in the inspected arXiv papers, OpenAlex record
and cited-by query, or target-specific GitHub searches. Scholar was
blocked, Semantic Scholar returned 429, and MathDB was unavailable.
The formal-conjectures path index had no match; its full contents were
not searched. Citation indexing can lag. This supports
`not-found-in-searched-scope`, not exhaustive novelty or priority.
