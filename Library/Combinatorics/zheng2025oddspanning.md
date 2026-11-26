---
bibkey: zheng2025oddspanning
authors: Jingyu Zheng and Baoyindureng Wu
year: 2025
title: Odd spanning trees of a graph
doi: null
url: https://arxiv.org/abs/2503.17676v1
claim: "Section 5(2) asks when a line graph has an odd spanning tree."
strata_touched:
  - D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree
license: citation-only
triage: anchor
---

# Odd spanning trees of a graph

## Verified locator

Primary version: https://arxiv.org/abs/2503.17676v1  
Full text: https://arxiv.org/pdf/2503.17676v1

Section 1, pp. 1–2, fixes finite simple graphs and defines an odd spanning tree
as a spanning tree in which every vertex has odd degree. Section 5(2), p. 17, asks:

> More specifically, when does a line graph have an odd spanning tree?

The surrounding question concerns connected claw-free graphs. The narrower
line-graph question is the subject of the
[problem dossier](../../Problems/zheng-wu-2025-odd-line-spanning-trees.md).

## Structural answer

Let $F$ be a finite undirected simple graph with $m$ edges. Its line graph
has a nonempty odd spanning tree exactly when $m$ is positive and even
and the following vertex splits are possible. Partition the edges
incident to each vertex into nonempty blocks, retaining the original
vertex as a tag. Each edge joins its two endpoint blocks in a graph $T$.
Require $T$ to be a tree and each block of degree at least two to have
at least two odd-order components after its deletion.

The theorem `D5/S3/Combinatorics/Graph/Incidence/ZhengWuOddLineTree.result` uses
Mathlib's line graph on the actual edge type. The criterion includes
isolated vertices, disconnected roots, empty edge sets and odd edge
counts. Isolated vertices have no blocks.

## Related exact tests

Xu and Xu's Theorem 2.4 extracts the all-odd degree terms of the
multivariate spanning-tree polynomial of a connected graph of even
order. Its count decides existence by positivity. Applying it to the
connected line graph of the component of $F$ carrying all its edges
gives an exact algebraic test. If several components carry edges, the
line graph is disconnected. [Xu and Xu, Theorem 2.4](https://arxiv.org/abs/2602.08179)

Zhou and Bu's Theorem 6.12 gives the weighted spanning-tree enumerator of
the line graph in terms of the connected root. For line edges whose weight
is the product of the two corresponding root-edge variables, the
exponent of each variable is the corresponding vertex degree in the
line-graph spanning tree. Thus their formula can supply the polynomial
used by the parity test. Their Remark 6.13 locates the natural
endpoint clique partition of the line graph.
[Zhou and Bu, Theorem 6.12 and Remark 6.13](https://doi.org/10.1007/s10801-020-00969-w)

Berget, Manion, Maxwell, Potechin and Reiner use endpoint-local forest
structures in their analysis of critical groups. Yan and Wang study
general degree and congruence constraints and give enumerations for
complete and complete bipartite hosts. The texts screened for the
[preregistration](https://github.com/the-omega-institute/trureturing/issues/31442)
did not supply the incidence-partition and branch equivalence. The
bounded comparison leaves unindexed literature and inaccessible full
texts unverified. [Berget et al.](https://arxiv.org/abs/0904.1246) ·
[Yan and Wang](https://arxiv.org/abs/2608.11990)
