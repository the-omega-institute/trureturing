---
bibkey: moutsinas2021hierarchy
authors: Giannis Moutsinas; Choudhry Shuaib; Weisi Guo; Stephen Jarvis
year: 2021
title: "Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks"
doi: 10.1038/s41598-021-93161-4
url: https://arxiv.org/abs/1908.04358v4
claim: "For a weighted simple directed graph with in-degree vector d and M the transpose of the in-degree Laplacian diag(d) - A, the forward hierarchical levels g are the minimum-norm minimizer of the residual of M x = d, and the forward democracy coefficient is 1 minus the arc-weighted mean of g_j - g_i over the arcs from i to j. The paper conjectures (Conjecture 3.6 of the journal version) that the forward and backward democracy coefficients of a weakly connected directed graph are at most 1, with equality exactly for balanced graphs."
strata_touched:
  - D5/S3/Combinatorics/Graph/HierarchyDemocracyRefutation
license: citation-only
triage: anchor
---

# Graph hierarchy: a novel framework to analyse hierarchical structures in complex networks

G. Moutsinas, C. Shuaib, W. Guo and S. Jarvis, arXiv:1908.04358 (v4
2020-10-07, "Graph Hierarchy: A novel approach to understanding hierarchical
structures in complex networks"); Sci. Rep. 11, 13943 (2021). Subjects:
physics.soc-ph, cross-listed to math.CO.

For a weighted simple directed graph with weights `a_ij ≥ 0`, in-degree
vector `d_j = Σ_i a_ij`, in-degree Laplacian `L = diag(d) − A` and `M = Lᵀ`,
the forward hierarchical levels are the minimum-norm minimizer of
`‖M x − d‖₂`, and the forward democracy coefficient is
`η_f = 1 − Mean(g_j − g_i)`, the mean over the arcs `i → j` weighted by
`a_ij`; the backward quantities use the out-degree Laplacian. The paper
proves `η_f, η_b ≥ 0` for weakly connected graphs and `η_f = η_b = 1` for
balanced graphs, and states:

> Let $G$ be a weakly connected directed graph. Then the following are true:
> $\eta_f(G) \le 1$ and $\eta_b(G) \le 1$; $\eta_f(G)=\eta_b(G)=1$ if and only
> if the graph is balanced.

## Verified locator

- DOI: https://doi.org/10.1038/s41598-021-93161-4 (Conjecture 3.6 of the
  journal version; the published text was read by a scout subagent).
- URL: https://arxiv.org/abs/1908.04358v4 (source retrieved 2026-10-01): the
  setting (`incl/part_prel_1.tex`), the Laplacians (`incl/part_prel_2.tex`),
  Definition 3.1 of the hierarchical levels (`incl/part_HLHD_1.tex`), and
  Definition 3.2 and the conjecture (`incl/part_HLHD_2.tex`).
