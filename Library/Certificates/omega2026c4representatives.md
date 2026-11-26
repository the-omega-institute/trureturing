---
bibkey: omega2026c4representatives
authors: "The Omega Institute repository contributors"
year: 2026
title: "Exact sub-quorum values from C4-free pair packing"
doi: null
url: https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/C4_FREE_REPRESENTATIVE_EQUALITY.md
claim: "Equal-side regular C4-free bipartite graphs have a proved threshold for equality of three finite parameters, with excess and optimal-support bounds."
strata_touched:
  - D5/S3/Combinatorics/Graph/SubQuorum/C4RepresentativeBounds
  - D5/S3/Combinatorics/Graph/SubQuorum/DissociationColoring
license: Apache-2.0
triage: anchor
---

# C4-free representative bounds

## Verified locator

URL: https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/C4_FREE_REPRESENTATIVE_EQUALITY.md

## Statement and scope

The source derives the upper comparison between the sub-quorum coloring
maximum and the representative-pair maximum from Sahbi's representative
reduction. A feasible pair contains matching edges and disjoint singletons.
Each singleton has at most one neighbor in the occupied vertex set. The
maximum induced degree-one selection gives the lower coloring bound through
an injective coloring of its support.

In a finite D-regular C4-free bipartite graph with N vertices in each part
and D at least three, each unordered pair of unused neighbors has at most
one singleton owner. Counting pairs on each side bounds the positive
excess and implies equality of the three maxima whenever
N ≤ 2(D−1)(D−2)+4. At the first size beyond this threshold an objective
of N+1 forces the matching to be empty. For objective N, the unused count
on each side is zero or at least (D−1)(D−2)+1. If N ≤ 2(D−1)(D−2)+1,
all singletons lie on one side and every vertex on that side is occupied.

For projective-plane incidence graphs, substitute D=q+1 and N=q²+q+1.
The threshold applies at every order q≥2. The one-side support bound
applies at q≥3. The order-two pair in the source has three singletons on
each side and one matching edge. The graph-specific Pappus and Heawood
certificates are outside the scope of these general modules.

## Attribution

The written source is [the pinned research note](https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/docs/C4_FREE_REPRESENTATIVE_EQUALITY.md).
The note credits Rafik Sahbi, *Sub-quorum colorings of graphs*,
[arXiv:2609.25128v1](https://arxiv.org/abs/2609.25128v1), for the
representative reduction. The source authors make no priority claim.

The owner uniqueness argument and the integer inequalities have a
[pinned Lean source](https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/formal/StarForming/C4FreeRepresentatives.lean). The graph-level
packing proof instantiates these inequalities with the actual singleton,
matching and unused counts. The Lean source uses Mathlib's graph degree
and finite sets to state these conditions over all finite simple graphs.

Sub-quorum colorings research artifact. Copyright 2026 The Omega Institute
and contributors. The source publishes its [Apache-2.0 license](https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/LICENSE)
and its [NOTICE](https://github.com/the-omega-institute/subquorum-colorings/blob/48728b42d39ab3de5de251c61da5a404ec418a69/NOTICE).
The repository's root [LICENSE](../../LICENSE) is the same Apache-2.0 text.
The source [NOTICE](../../docs/reports/licenses/subquorum-colorings-NOTICE.txt)
is reproduced verbatim.
