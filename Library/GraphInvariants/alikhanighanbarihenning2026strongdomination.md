---
bibkey: alikhanighanbarihenning2026strongdomination
authors: Saeid Alikhani, Nima Ghanbari, Michael A. Henning
year: 2026
title: "Strong domination number of graphs from primary subgraphs"
doi: 10.2989/16073606.2025.2574046
url: https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046
claim: "Problem 1, Inequality (4): γst(G) ≥ γst(G1) + γst(G2) − 1 − ΣX,Y for every r ≥ 2."
strata_touched:
  - D5/S3/Combinatorics/Graph/Domination/AlikhaniGhanbariHenningCliqueGluing
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.2989/16073606.2025.2574046

Source: https://www.tandfonline.com/doi/full/10.2989/16073606.2025.2574046

Quaestiones Mathematicae 49(2), 195–211. The journal statement is distinct from
Question 1 of the superseded preprint https://arxiv.org/abs/2306.01608v1.

Abstract, p. 195: "A set D of vertices is a strong dominating set in a graph G, if for every vertex x ∈ V(G) \ D there is a vertex y ∈ D with xy ∈ E(G) and deg(x) ≤ deg(y). The strong domination number γst(G) of G is the minimum cardinality of a strong dominating set in G."

Section 1, p. 196: "Choose a clique of cardinality r from each Gi, i = 1, 2, and form a new graph G from the union of G1 and G2 by identifying the two chosen r-cliques in an arbitrary manner."

Problem 1, p. 202: "For r ≥ 2, let G1 and G2 be connected graphs both of order at least r + 1 that contain r-cliques A = {u1, u2, …, ur} and B = {v1, v2, …, vr}, respectively. Let Xi = NG1(ui) \ A and Yi = NG2(vi) \ B for i ∈ [r], and let ΣX,Y = Σ_{i=1}^r |Xi| + Σ_{i=1}^r |Yi|. Let G ∈ G1 ∪Kr G2 be obtained by a Kr-gluing of the graphs G1 and G2 by identifying the cliques A and B, where we identify the vertices ui and vi for i ∈ [r]. Determine a best possible lower bound on γst(G) in terms of γst(G1), γst(G2) and ΣX,Y. In particular, is it true that γst(G) ≥ γst(G1) + γst(G2) − 1 − ΣX,Y? (4)"

The finite vertex labels in Lean use Fin r with index i corresponding to the
source's i+1. Clique embeddings enumerate distinct vertices; their ranges are
cliques. The glued vertex type is V1 ⊕ {w : V2 // w ∉ Set.range B}; embedRight
identifies B i with A i. The graph is SimpleGraph.fromRel of the union of the
two edge relations. X uses neighborFinset minus the enumerated clique, and
sigmaXY sums the two families of cardinalities. The strong domination number
is the natural-number infimum of attained finite-set sizes. The inequality
uses integer subtraction.

The result proves Inequality (4) for all r ≥ 2 under the stated hypotheses.
The source's general sharpness family is outside the Lean claim. The source's
other results are not altered by this inequality. Finer-parameter bounds
remain open here. Literature-screen completeness is ASSUMED-UNVERIFIED.
