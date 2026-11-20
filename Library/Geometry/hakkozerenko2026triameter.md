---
bibkey: hakkozerenko2026triameter
authors: Artem Hak and Sergiy Kozerenko
year: 2026
title: Triameter, distance packings, and vertex connectivity
doi: 10.48550/arXiv.2611.17259
url: https://arxiv.org/html/2611.17259v1#S7.p2.1
claim: "The paper proves the independence bound and the equality constraints on triametral distances. Question 1 asks for the graph classification, at least for k = 1."
strata_touched:
  - D5/S3/Combinatorics/Graph/Triameter/CliqueChains
  - D5/S3/Combinatorics/Graph/Triameter/DistanceProjection
license: citation-only
triage: anchor
---

# Triameter equality at k = 1

ArXiv:2611.17259v1, §7, Question 1, printed p. 19.

> Question 1. Theorem 1.1 determines the distances between the vertices of a triametral triple in graphs attaining the equality in (1), but not the whole graph. Characterize the graphs attaining this equality, at least for k = 1, that is, the graphs G with tr(G) = 4α(G) − 1.

The source considers finite simple connected graphs of order at least three. The repository's `CliqueChains.question1` gives the classification at k = 1. The classification at general positive k remains open here.

- `EvenLegTriangle.Vertex` and `EvenLegTriangle.H` give leg and depth coordinates and adjacency for the graph U(2q₀, 2q₁, 2q₂), the even-leg specialization of the triangle with attached paths. [§2.1, pp. 3–4, Figure 1](https://arxiv.org/html/2611.17259v1#S2.SS1)
- `perimeter` and `triameter` are the sum of the three pairwise distances and its maximum over triples. The formal definitions use ordered triples with repeats, which preserve the maximum at order at least three. Mathlib's distance is zero for unreachable pairs, and the finite supremum is zero on the empty vertex type. [§2.2, p. 4](https://arxiv.org/html/2611.17259v1#S2.SS2)
- `triameter_le_indepNum` writes tr(G) ≤ 4α(G) − 1 as tr(G) + 1 ≤ 4α(G). At connected orders one and two, α(G) = 1 and the triameter is respectively 0 and 2. [§5, Corollary 5.1, inequality (5), p. 11](https://arxiv.org/html/2611.17259v1#S5.E5)
- `k1_equality_projection` specializes the equality part of the proof of Theorem 1.1 to k = 1, where 1-packings are independent sets. The equality distances d(aᵢ,aⱼ) = 2(qᵢ + qⱼ) + 1 and q₀ + q₁ + q₂ = α(G) − 1 give odd perimeter and leg lengths 2qᵢ by Definition 3.1 and equation (3). Lemma 3.2 supplies the vertex-surjective, non-expanding map and an edge lift for every model edge. The formal conclusion uses the edge-or-collapse form of non-expansion from §2.1. Equality is impossible at connected orders one and two. [§4, proof of Theorem 1.1, p. 10](https://arxiv.org/html/2611.17259v1#S4.p19.1) · [§3, Definition 3.1 and equation (3), p. 5](https://arxiv.org/html/2611.17259v1#S3.E3) · [§3, Lemma 3.2, p. 6](https://arxiv.org/html/2611.17259v1#S3.Thmtheorem2.2)
- `triameter_ge_of_evenLegTriangle` is the repository's converse estimate for an arbitrary surjective edge-or-collapse map. It applies the model foot distances to three chosen preimages. [§2.1, non-expansion, p. 4](https://arxiv.org/html/2611.17259v1#S2.SS1) · [§2.2, Lemma 2.5(2), p. 5](https://arxiv.org/html/2611.17259v1#S2.Thmtheorem5)
