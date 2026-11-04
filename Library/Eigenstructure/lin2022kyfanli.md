---
bibkey: lin2022kyfanli
authors: Zhen Lin, Lianying Miao, Guanglong Yu and Han Sheng
year: 2022
title: "On the Ky Fan k-norm of the LI-matrix of graphs"
doi: 10.13001/ela.2022.5943
url: https://arxiv.org/abs/2012.11162v2
claim: "Conjecture 5.11 asserts uniqueness of the connected graph G_{m,n} maximizing the second and third Ky Fan norms of the centered Laplacian."
strata_touched:
  - D5/S3/Combinatorics/Graph/KyFanGap/LinMiaoYuShengSecondNormUniquenessRefutation
license: citation-only
triage: anchor
---

# Second Ky Fan norm uniqueness

## Verified locator

DOI: 10.13001/ela.2022.5943

Source: https://arxiv.org/abs/2012.11162v2

Journal: *Electronic Journal of Linear Algebra* 38, 680–696.
The source is arXiv:2012.11162v2; the journal page numbers below refer to
the [published PDF](https://journals.uwyo.edu/index.php/ela/article/download/5943/5921).

## Source statements

The introduction, page 681, states:

> Let G be a graph with n vertices and m edges. Then the LI-matrix of G is defined as LI(G)=L(G)−(2m/n)Iₙ.

Section 2 of arXiv v2 (journal page 682) states:

> The Gₘ,ₙ, shown in Fig. 2.1, is a graph with n vertices and m edges which has m−n+1 triangles with a common edge and 2n−m+3 pendent edges incident with one end vertex of the common edge.

Conjecture 5.11, page 694, states:

> Among all connected graphs with n and m edges n ≤ m ≤ 2n−3, the Gₘ,ₙ is the unique graph with maximal value of ‖LI(G)‖F₂ and ‖LI(G)‖F₃.

Theorem 5.9, page 693, states:

> Let Bₙ be a bicyclic graph with n vertices. Then ‖LI(Bₙ)‖F₂ ≤ ‖LI(Gₙ₊₁,ₙ)‖F₂ with equality if and only if Bₙ ≅ Gₙ₊₁,ₙ.

## Encoding and scope

The phrase “with n and m edges” denotes n vertices and m edges. On the
conjecture's range n ≤ m and m+3 ≤ 2n, the graph
in the figure and the stated order and size give 2n−m−3 pendant vertices;
the printed 2n−m+3 is inconsistent with these cardinalities. On vertices
0,…,n−1, vertex 0 is universal and vertex 1 is adjacent to vertices
2,…,m−n+2. The Lean function Gmn takes n first, m second. The predicate
claim asserts the maximum and its equality characterization separately
for k=2 and k=3; it does not encode simultaneous maximization.

At n=6 and m=7, replacing the two extra edges {1,2},{1,3} by
{1,2},{3,4} gives a connected nonisomorphic graph with the same second
norm 6. The degree lists distinguish the graphs, and exact rational
diagonalizations give their centered spectra. This refutes the separate
second-norm uniqueness clause and the equality assertion of Theorem 5.9.
The third-norm assertion, a general-order theorem, the global bound and
a replacement equality classification are outside this formal result.

## Experiment and literature boundary

The exact finite experiment is in
[`the-omega-institute/trureturing-experiments`](https://github.com/the-omega-institute/trureturing-experiments/tree/5ac15f4345d6fc41f30913cce150a4b5f46cc64b/docs/reports/lmys-kyfan-c511),
commit `5ac15f4345d6fc41f30913cce150a4b5f46cc64b`.
The command is `python3 docs/reports/lmys-kyfan-c511/check.py`;
the script SHA-256 is
`8506853201bc6073cd6ff13e7678ebeba3ab62286d067cbaef321bfc4b894507`.
Issue [#21801](https://github.com/the-omega-institute/trureturing/issues/21801)
reports exit 0 and final line `ALL_CHECKS_OK`, covering 6 ≤ n ≤ 18.
These finite computations are distinct from the kernel proof at n=6.

Literature completeness is `ASSUMED-UNVERIFIED`: the screen recorded on
#21801 found no earlier settlement in the works read, while citation
enumeration through OpenAlex and Semantic Scholar returned HTTP 429.
Exhaustive downstream dependence is unverified.
