---
slug: sahbi-2026-star-forming-bipartite-refutation
bibkey: sahbi2026upperstarforming
doi: 10.48550/arXiv.2610.03785
url: https://arxiv.org/abs/2610.03785v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result
---

# Sahbi's Conjecture 4.2: bipartite two-independence and upper star formation

## Problem

Rafik Sahbi, *Upper k-Star-Forming Sets, k-Independence, and Upper
Domination*, arXiv:2610.03785v2, Conjecture 4.2:

> For every bipartite graph G, β₂(G) = SF₂(G).

For a finite simple graph, a set I is k-independent when every vertex of
G[I] has degree less than k; βₖ(G) is the maximum such cardinality.
Definition 2.1 calls S k-star-forming if, for each v outside S,
G[S ∪ {v}] contains a copy of K₁,ₖ containing v. The copy need not be
induced. A star-forming set is minimal if no proper subset is
star-forming; SFₖ(G) is the maximum cardinality among these minimal sets.

The Lean `claim` quantifies over all n and all decidable simple graphs on
Fin n, assumes `Colorable 2`, and asserts `beta G 2 = SF G 2`.
The theorem `result : ¬ claim` refutes this statement. Fin n represents
every finite vertex type up to bijection, and all the defining adjacency,
subset and cardinality conditions are invariant under such a relabelling.

## Motivation

The paper proves equality for complete bipartite graphs and chain graphs.
Conjecture 4.2 proposes extending equality to all bipartite graphs. One
bipartite graph with unequal parameters settles that extension negatively.

## Gap

The supplied statement source identifies Conjecture 4.2 as open and cites
issue #14706 as its preregistration. No independent literature or priority
check is available in this offline implementation. The result concerns
the verbatim conjecture, without asserting a first settlement in the
literature.

## Route

Take vertices aᵢ = i and bⱼ = 5+j for 0 ≤ i,j < 5. The cross-edge matrix is

```text
1 1 0 0 1
1 1 0 1 0
0 0 0 1 1
0 1 1 1 1
1 0 1 1 1
```

There are 16 edges and no edges within either side. Colour vertices 0
through 4 by zero and vertices 5 through 9 by one.

For k = 2, the star definition is equivalent to this local criterion:
each v outside S either has at least two neighbours in S, or has a
neighbour u in S with at least one neighbour in S. Indeed, v is either
the centre or a leaf of the star. Conversely either alternative gives a
centre and two distinct leaves. When v is a leaf, its fellow leaf lies
in S and therefore differs from v.

Set S = {0,1,2,5,6,7}. The local criterion holds for S and fails for all
63 proper subsets, so S is minimal two-star-forming. Thus SF₂ ≥ 6.
All 210 six-element subsets fail two-independence. Any two-independent
set of size at least six would contain a six-element subset that remains
two-independent, because deleting vertices cannot increase the selected
degree. Hence β₂ ≤ 5 < 6 ≤ SF₂.

## Falsifier

The counterexample must have the specified edges, admit the stated
colouring, and use Definition 2.1 rather than an induced-star variant.
Both directions of the local equivalence are needed, as are failure on
every proper subset of S and the hereditary argument for larger
independent sets. Each obligation is part of the Lean proof of `result`.

## Evidence

`D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result`
has the closed type `¬ claim`. Its general local equivalence explicitly
constructs and extracts two-leaf stars. The finite certificates use
kernel reduction of decidable propositions. No `native_decide`, `sorry`
or new axiom is used. The axiom closure and measured compilation costs
are recorded in the implementation report.

## Triage

- [proved: D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.result]
  Conjecture 4.2 is false: the displayed bipartite graph satisfies
  β₂ ≤ 5 and SF₂ ≥ 6.
- [proved: D5/S3/Combinatorics/Graph/StarFormingDissociationRefutation.starForming_two_iff]
  Lemma 2.2's two-star local criterion is equivalent to Definition 2.1
  for arbitrary vertex types with decidable equality and adjacency.
- [computed: Python, enumerate all 1024 vertex masks with the displayed
  adjacency matrix, count selected neighbours, and test every proper
  submask for minimality]
  The exact values on this graph are β₂ = 5 and SF₂ = 6. These equalities
  are supplemental computations; the Lean theorem uses only the two
  separating bounds.
- [computed: read rows zero and one of the displayed matrix]
  This is not a chain graph. N(a₀) = {b₀,b₁,b₄} and
  N(a₁) = {b₀,b₁,b₃} are incomparable by inclusion, so neighbourhoods
  on this side are not nested. The example therefore does not contradict
  the paper's chain-graph theorem.
- [computed: supplied exhaustive C enumeration of every cross-edge set]
  Equality β₂ = SF₂ holds for every bipartite graph with part sizes
  (1,8), (2,7), (3,6), (4,5), (2,8), (3,7), and (4,6).
  Smaller splits embed into the nine-vertex splits by adding isolated
  vertices. Every isolated vertex belongs to every minimal star-forming
  set and can be added to a maximum two-independent set, increasing both
  parameters by one. Thus all bipartite counterexamples on at most nine
  vertices are excluded by the supplied computation and this reduction.
  The C program and its execution were not independently checked here.
- [derived: star plus isolated vertices, using the two-star local criterion]
  A graph with one part of size one is a star with d leaves plus t isolated
  vertices. If d ≤ 1, there is no two-leaf star; every vertex is mandatory
  for star formation and both parameters equal t+d+1. If d ≥ 2, the largest
  two-independent set in the star has size max(d,2). Its minimal
  two-star-forming sets are exactly all d leaves, or the centre together
  with one leaf. Indeed, omitting the centre forces every leaf to be
  selected; including it forces at least one leaf, and one leaf already
  suffices. Including the mandatory isolates gives
  β₂ = SF₂ = t+max(d,2). This includes the unenumerated (1,9) split.
  Together with the computed splits, every ten-vertex bipartite
  counterexample must have a 5+5 bipartition. The argument is mathematical
  prose and is not an additional Lean theorem.
- [computed: the same exhaustive C enumeration on the 5+5 split]
  Among the 2²⁵ edge sets between two labelled parts of size five,
  exactly 3600 give β₂ ≠ SF₂. Together with the
  exclusions above, this computation makes ten the smallest order of a
  bipartite counterexample.
- [computed: supplied exhaustive C subset computation on grids Pₘ□Pₙ]
  Equality β₂ = SF₂ holds for 1×1 through 1×10, 2×2 through 2×8,
  3×3 through 3×7, 4×4, and 4×5. These are finite computations,
  not a proof for all grids; their execution was not repeated here.
- [open] Conjecture 8.4 on grids remains open. The complete-bipartite
  and chain-graph theorems are not formally verified here.

## ASSUMED-UNVERIFIED

The paper title, version, verbatim definitions and conjecture, and the
stated complete-bipartite and chain-graph results are supplied source
attributions. The paper and issue #14706 have not been retrieved in this
offline implementation. No exhaustive literature or priority claim follows.
