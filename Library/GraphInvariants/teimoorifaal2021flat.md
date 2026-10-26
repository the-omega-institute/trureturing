---
bibkey: teimoorifaal2021flat
authors: H. Teimoori Faal
year: 2021
title: On Clique Roots of Flat Graphs
doi: 10.48550/arXiv.2112.09721
url: https://arxiv.org/abs/2112.09721v1
claim: "Conjecture 1 (p. 6): The class of 2-connected K₅-free flat graphs without isolated triangles has only clique roots. In particular, this class has always the clique root r = −1 of multiplicity 2."
strata_touched:
  - D5/S3/Combinatorics/Graph/CliquePolynomial/TeimooriFaalFlatCliqueRoots
license: citation-only
triage: anchor
---

# Teimoori Faal, *On Clique Roots of Flat Graphs*

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2112.09721

Source: https://arxiv.org/abs/2112.09721v1

The source is version 1. Equation (1) and the clique-count convention are on page 1; Definition 2.2 is on page 4; Definition 4.1 and Conjecture 1 are on page 6.

## Source statements

Page 1:

> For a given graph G, a complete subgraph of G with i-vertices (i ≥ 1) is called an i-clique of G.

Equation (1) defines C(G, x) = ∑_{k=0}^{ω(G)} c_k(G)x^k, followed by:

> where by convention c₀(G) is taken to be 1 for any simple graph G.

Definition 2.2, page 4:

> A graph G is called flat if every edge of G belongs to at most two triangles of G.

Definition 4.1, page 6:

> For a triangle δ = {u, v, w} ⊂ V(G), the value of δ in G denoted by val_G(δ) is defined by val_G(δ) = N_G(u) ∩ N_G(v) ∩ N_G(w). Moreover, a triangle is called isolated if its triangle value is zero.

Conjecture 1, page 6:

> The class of 2-connected K₅-free flat graphs without isolated triangles has only clique roots. In particular, this class has always the clique root r = −1 of multiplicity 2.

Page 4:

> we will call a real root of C(G, x) a clique root of G.

## Scope

The formal refutation uses the graph on twelve vertices whose four complete blocks are {0,1,4,5}, {1,2,6,7}, {2,3,8,9}, and {3,0,10,11}. It meets all the graph hypotheses. Its clique polynomial 1+12x+24x²+16x³+4x⁴ has a nonreal complex zero. The formal result refutes the main clause, without using the multiplicity clause. It makes no assertion about the source's K₄-free theorems.

The preregistration's literature screen found no settlement of Conjecture 1. Completeness of that screen is ASSUMED-UNVERIFIED.
