---
slug: zhou-strong-reverse-degree-six
bibkey: zhou2026deltay
doi: 10.48550/arXiv.2609.08963
url: https://arxiv.org/html/2609.08963v1#S2.p8.1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.zhou_sharp_threshold
---

# Zhou’s sharp degree-six threshold for strong reverse moves

## Problem

Zhichen Zhou asks immediately after Lemma 10, “We conjecture that the tight condition for this lemma is δ(G) ≥ 6.” Let $P(d)$ assert equality up to isomorphism of the ordinary and strong reachable families for every finite simple graph with all vertex degrees at least $d$. Is $P(6)$ true and $P(d)$ false for each natural $d<6$? A forward step replaces a triangle by a degree-three center. A reverse step deletes a degree-three center and takes the simple-edge union with the three neighbor pairs. It is strong precisely when those neighbors are independent. Histories include the empty sequence. [Zhou, Definitions 3 and 5 and §2 after Lemma 10](https://arxiv.org/html/2609.08963v1#S2.p8.1)

## Motivation

The minimum degree of the starting graph controls when imposing independence at each reverse site leaves the reachable family unchanged.

## Gap

Lemma 10 gives sufficiency at seven. At six the forward-only argument no longer applies, since a vertex of original degree six may be available for a reverse move. [Zhou, Lemma 10](https://arxiv.org/html/2609.08963v1#Thmtheorem10) · [Preregistration #33461](https://github.com/the-omega-institute/trureturing/issues/33461)

## Route

Color all initial vertices alike. Give a crossing edge weight two and a same-color edge weight one. Maintain weighted degree at least six at every vertex, monochromatic triangles, and absence of a four-cycle of crossing edges. A forward move gives the center the opposite color from the triangle. A reverse center has three crossing spokes, and monochromaticity of triangles forces its neighbors to be independent. An all-crossing four-cycle through the reverse center would be needed for a newly inserted pair to close a mixed triangle. The invariant passes to every step.

For sharpness use the complete graph on 0 through 6 with pairs 06 and 14 deleted. The five steps are forward on 012 at 7, forward on 034 at 8, reverse at 0, forward on 157 at 9, and reverse at 1. The last center has neighbors 3, 6 and 9, with 36 the unique old pair. The edge counts are 19, 19, 19, 19, 19 and 18. Each strong step preserves cardinality, as does graph isomorphism.

## Falsifier

An ordinary reachable graph at minimum degree six with no isomorphic strong endpoint would refute sufficiency. For the specific sharpness argument, an invalid move or a strong endpoint isomorphic to the 18-edge endpoint would break the proposed separation.

## Evidence

The theorem `D5/S3/Combinatorics/Graph/DeltaY/SharpThreshold.zhou_sharp_threshold` asserts $P(6)\land\forall d<6,\neg P(d)$. The simple-graph model uses an equivalence with an option type to account for all surviving vertices and the added or removed center. Lifting to finite active natural labels preserves the move relation and degree, and permits a fresh label for each forward step. The sharpness seed has minimum degree five.

## Triage

Tier 1 theorem. The full conclusion is proved with a symbolic history invariant and a finite witness for sharpness. The admission basis is open-problem resolution.

## ASSUMED-UNVERIFIED

Global priority remains unverified. The bounded prior-resolution search covers the paper and the related works named in the preregistration. [Preregistration #33461](https://github.com/the-omega-institute/trureturing/issues/33461)
