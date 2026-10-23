---
bibkey: apteparekhsud2025tokenbounds
authors: Anuj Apte; Ojas Parekh; James Sud
year: 2025
title: Conjectured Bounds for 2-Local Hamiltonians via Token Graphs
doi: null
url: https://arxiv.org/abs/2506.03441v2
claim: Appendix Conjecture 7 bounds the least token-graph adjacency eigenvalue by minus half the sum of maximum cut and size-restricted matching weights.
strata_touched:
  - D5/S3/Combinatorics/Graph/TokenGraph/CutBoundRefutation
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2506.03441v2

Version 2, 27 May 2026; Conjecture 7 and Corollary 12, page 39;
cut and matching conventions, page 8; matrix notation and token graph, page 9.

## Statement

Page 39, Appendix D.2, “Upper bounds based on maximum cut”:

> In contrast, the following bound was shown to hold on our dataset
>
> **Conjecture 7.** For all $G$ and for all $1 \le k \le \lfloor n/2\rfloor$
>
> $$\lambda_{min}(A(F_k(G))) \ge -\frac{C(G)+M_k(G)}{2}.$$

Page 8:

> Let $\delta(S)$ be the set of edges in $G$ that cross from $S$ to $V \setminus S$, and $Cut(S)$ be the sum of the weights of the edges $\delta(S)$. We denote the maximum of $Cut(S)$ over all $S$ by $C(G)$, i.e., $C(G)$ is the solution to the Maximum Cut (MaxCut) problem on $G$.

> Let $M_k(G)$ denote the maximum weight matching under the restriction that $|M|\leq k$.

Page 9:

> Let $\lambda_{max}(\cdot)$, $\lambda_{min}(\cdot)$, and $eigs(\cdot)$ describe the maximum eigenvalue, minimum eigenvalue, and the set of unique eigenvalues of a matrix.

Definition 1 on page 9 defines the token graph on the $k$-subsets of $[n]$:

> Edges: vertices $A$ and $B$ are connected by an edge if and only if their symmetric difference $A\triangle B = \{a,b\}$, where $a\in A$, $b\in B$, and $(a,b)\in E$.

The unweighted specialization takes every edge weight to be one. Finite subsets
represent cuts; each unordered crossing edge is counted once. A matching is an
edge subset whose distinct edges have disjoint endpoint sets. Its weight is its
cardinality. The minimum eigenvalue is the infimum of the real Hermitian
eigenvalue family of the real adjacency matrix. Labels `Fin n` correspond
bijectively to the source's labels $[n]$.

## Refutation

The blow-up of the five-cycle with 40 vertices in each independent block has
200 vertices. For 100 tokens, a phase product with $z=(-4+3i)/5$ has Rayleigh
quotient $-646912/199$. Its maximum cut is at most 6400 and every matching with
at most 100 edges has weight at most 100. Thus the conjectured lower bound is
at least $-3250$, exceeding that Rayleigh quotient by $162/199$.

The token graph is the existing finite-subset construction
`TokenGraphLaplacianRadiusRefutation.tokenGraph`. The refutation concerns
Conjecture 7, independently of the paper's other token-graph conjectures.
