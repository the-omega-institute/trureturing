---
bibkey: zhangtian2025steinerradius
authors: Qingnan Zhang; Yingzhi Tian
year: 2025
title: On the Steiner k-diameter and Steiner (k, k′)-radius of trees
doi: 10.48550/arXiv.2511.22492
url: https://arxiv.org/abs/2511.22492v1
claim: "Conjecture 5.1 bounds every finite tree's Steiner k-diameter by k/(k−k′) times its Steiner (k,k′)-radius minus k′(k′−1)/(k−k′)."
strata_touched:
  - D5/S3/Combinatorics/Graph/Eccentric/ZhangTianSteinerTreeRadius
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2511.22492

Source: https://arxiv.org/abs/2511.22492v1

## Source definitions

Page 1 fixes graph size as |E(G)| and considers finite simple connected graphs.
Page 2 states:

> The Steiner distance d_G(S) among the vertices of S (or simply the distance of S) is defined as the minimum size among all connected subgraphs whose vertex sets contain S.

> The Steiner k-eccentricity ε_k(v; G) of a vertex v in G is defined by max{d_G(S) : v ∈ S ⊆ V(G), |S| = k}, where k ≥ 2.

> The Steiner k-radius of G is Sr_k(G) = min{ε_k(v) : v ∈ V(G)}, and the Steiner k-diameter of G is Sd_k(G) = max{ε_k(v) : v ∈ V(G)}.

> The Steiner (k, k′)-eccentricity ε_{k,k′}(S′; G) of a k′-subset S′ in G is defined as the maximum Steiner distance over k-subsets of V(G) that include S′, that is, ε_{k,k′}(S′; G) = max{d_G(S) : S′ ⊆ S ⊆ V(G), |S| = k}, where k ≥ 2 and k ≥ k′ ≥ 1.

> The Steiner (k, k′)-radius of G is Sr_{k,k′}(G) = min{ε_{k,k′}(S′; G) : S′ ⊆ V(G), |S′| = k′}, where k′ ≥ 1.

## Conjecture 5.1

Page 14 states:

> Let n, k, k′ be integers with n ≥ k ≥ 3 and k > k′ ≥ 1 and let T be a tree with order n. Then Sd_k(T) ≤ k/(k − k′) Sr_{k,k′}(T) − k′(k′ − 1)/(k − k′).

The formal definitions take natural infima and suprema of the displayed
edge counts. The conjecture uses rational casts, so its subtractions and
divisions are rational operations. The finite type's cardinality is n.

## Scope

The proof in ZhangTianSteinerTreeRadius uses the full anchor hull in a
terminal-cut average. Its pointwise inequality permits overlapping terminal
sets and an arbitrary k-set, without requiring it to attain the diameter.
The r=1 and r=k−1 endpoints are included. A classification of equality and
a version of the pointwise inequality for nonnegative weighted trees have
not been formalized here.

Conjecture 5.1 is followed by References. No subsequent source theorem
depends on the conjecture. The literature screen in issue #20671 found no
settlement in the searched sources; literature completeness is
ASSUMED-UNVERIFIED.
