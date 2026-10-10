---
slug: sahbi-2026-star-forming-triangle-free-refutation
bibkey: sahbi2026upperstarforming
doi: 10.48550/arXiv.2610.03785
url: https://arxiv.org/abs/2610.03785v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.result
---

# Sahbi's Conjecture 7.2: triangle-free equality at two

## Problem

Rafik Sahbi, *Upper k-Star-Forming Sets, k-Independence, and Upper
Domination*, arXiv:2610.03785v2, Conjecture 7.2:

> For every triangle-free graph G, β2(G) = SF2(G).

A set I is k-independent when every vertex of the induced graph G[I]
has degree less than k. The maximum such cardinality is βₖ(G).
A set S is k-star-forming when, for every outside vertex v,
G[S ∪ {v}] contains a copy of K₁,ₖ containing v. The copy need not
be induced. SFₖ(G) is the maximum cardinality of an inclusion-minimal
k-star-forming set.

The Lean `claim` quantifies over every n and every simple graph G on
Fin n with decidable adjacency, assumes `G.CliqueFree 3`,
and asserts `beta G 2 = SF G 2`.
Every finite simple graph can be relabelled onto Fin n; all defining
adjacency, subset and cardinality conditions are invariant under this
bijection. Positive integers k correspond exactly to naturals with 1 ≤ k.
The theorem `result : ¬ claim` refutes the quoted statement.

## Motivation

Triangle-free graphs include every bipartite graph, so the two-star bipartite counterexample also tests this broader equality.
The conclusion concerns this separately stated conjecture.

## Gap

The supplied literature-check reading states that arXiv v1 (30 Sep 2026)
and v2 (6 Oct 2026) both state Conjecture 7.2, with no later version
or citing work found by title, identifier, author, and star-forming
bipartite or triangle-free queries. The offline repository query found
no other record of this conjecture before these corollary dossiers.
The external reading is supplied evidence, not an independently repeated
literature or priority check.

## Route

The imported two-star refutation uses a ten-vertex bipartite graph whose
cross-edge matrix is

```text
1 1 0 0 1
1 1 0 1 0
0 0 0 1 1
0 1 1 1 1
1 0 1 1 1
```

Its two-independence number is at most five and its upper two-star-forming
number is at least six. The imported theorem refutes equality on all
bipartite graphs at two using these bounds.

Every two-colourable graph is triangle-free: a clique of size three requires three distinct colours. Mathlib `SimpleGraph.Colorable.cliqueFree` applies with 2 < 3. Consequently the displayed graph is triangle-free. Equality on every triangle-free graph would give equality on this bipartite graph, contradicting the imported refutation.

## Falsifier

The imported claim must use the same β and SF definitions, including
inclusion-minimality and non-induced star copies. The implication from
this conjecture to the bipartite equality at two must retain every graph
and adjacency decision instance; two-colourability must imply absence of three-cliques.
These obligations are checked by the Lean proof.

## Evidence

`D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.result`
has the closed type `¬ claim` and applies
`D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result`.
The module imports and reuses the existing definitions without adding
finite computation. It uses no `sorry`, `native_decide`, or new axiom.
The implementation report records compilation and axiom closure.

## Triage

- [proved: D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation.result]
  Conjecture 7.2 is false by the bipartite counterexample at k = 2.
- [proved: D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result]
  The underlying graph satisfies β₂ ≤ 5 < 6 ≤ SF₂.
- [open] This refutation does not classify other triangle-free graphs.

## ASSUMED-UNVERIFIED

The paper title, versions, verbatim conjecture, and external literature
check are supplied source attributions. Neither arXiv nor GitHub issue
#14706 was retrieved during this offline task. No independent firstness
claim or complete external literature search is asserted.
