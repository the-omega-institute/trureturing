---
bibkey: wangqinxia2025unexpectedautomorphisms
authors: Xiaomeng Wang, Yan-Li Qin, Binzhou Xia
year: 2025
title: "The existence of unexpected automorphisms in direct product graphs"
doi: 10.48550/arXiv.2509.26170
url: https://arxiv.org/abs/2509.26170v2
claim: "Conjecture 1.3 asserts that a nontrivial loopless graph pair with bipartite second factor is stable exactly when its first factor is stable."
strata_touched:
  - D5/S3/Combinatorics/Graph/Products/WangQinXiaLooplessStabilityRefutation
license: citation-only
triage: anchor
---

# Stability and automorphism groups of direct products

## Verified locator

DOI: 10.48550/arXiv.2509.26170

Source: https://arxiv.org/abs/2509.26170v2

The cited version is v2. The graph category and Definition 1.1 are on page 1;
Conjecture 1.3 and Theorem 1.4 are on page 2.

## Source statements

Page 1: “In this paper, all graphs are finite and undirected, without multiple edges but possibly with loops.”

Page 1: “In other words, (Γ,Σ) is stable if and only if (1) is an equality.” Equation (1) is $\operatorname{Aut}(\Gamma)\times\operatorname{Aut}(\Sigma)\leq\operatorname{Aut}(\Gamma\times\Sigma)$, with componentwise action.

Page 1: “Indeed, a graph Γ is stable in the sense of [7] if and only if the pair (Γ,K₂) is stable.”

Page 1: “A graph is called twin-free if no two vertices have the same neighborhood in the graph.”

Page 1: “We say that graphs Γ and Σ are coprime (with respect to the direct product) if there exists no graph Δ of order greater than 1 such that Γ ≅ Γ′×Δ and Σ ≅ Σ′×Δ for some graphs Γ′ and Σ′.”

Definition 1.1, page 1: “A graph pair (Γ,Σ) is nontrivial if Γ and Σ are coprime connected twin-free graphs and exactly one of them is bipartite.”

Conjecture 1.3, page 2: “Let (Γ,Σ) be a nontrivial graph pair without loops, where Σ is bipartite. Then (Γ,Σ) is stable if and only if Γ is stable.”

## Mathematical scope

The Lean predicates use finite vertex types, `SimpleGraph` for the two loopless
graphs, `SimpleGraph.Iso` for automorphisms, and the categorical product
`DirectProductCyclePathBootstrap.dirProd`. Stability says that every product
automorphism comes from one automorphism of each factor. Single-graph stability
uses the complete loopless graph on `Fin 2`.

Coprimality quantifies over every finite symmetric common factor and both
cofactors, including graphs with loops. Labelling those graphs by `Fin` preserves
all finite isomorphism classes. `RationalPositiveRealization.LoopGraph` supplies
that symmetric relation. Twin-freeness is injectivity of the open-neighborhood
map. `Nontrivial` retains all of Definition 1.1, including exactly one bipartite
factor, in addition to the separate bipartiteness hypothesis of Conjecture 1.3.

The loopless family, its two-fold-automorphism classification, and the
coprimality obstruction are repository-derived results. They are not attributed
to this source. The source's Theorem 1.4(a) proves the reverse implication under
the original hypotheses. Its conditional sufficient results and its cycle
results retain their own hypotheses; the refutation concerns Conjecture 1.3.
