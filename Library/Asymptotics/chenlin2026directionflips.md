---
bibkey: chenlin2026directionflips
authors: Hao Chen and Yupeng Lin
year: 2026
title: Oriented Paths with Few Direction Flips Are Tournament Anti-Sidorenko
doi: 10.48550/arXiv.2609.14655
url: https://arxiv.org/abs/2609.14655v1
claim: "Question 6.1 asks whether the exact strict-flip threshold f(k), divided by k, converges."
strata_touched:
  - D5/S3/Combinatorics/ExtremalDensity/ChenLinFlipLimit
license: citation-only
triage: anchor
---

# Chen and Lin: direction flips in tournament paths

## Verified locator

DOI: 10.48550/arXiv.2609.14655

Original source: https://arxiv.org/abs/2609.14655v1

Source archive: https://arxiv.org/src/2609.14655v1

The archive SHA-256 is `50d20f9f28ab013a504ce089320c4c92fe20dbbb4cefbf1133246f237976a7da`.
The file `direction_flips_final.tex` has SHA-256
`127b489db360746c75df4899acb6cc3cb4a71c49b87666aa771bc1d86f67df10`.

Section 1 defines homomorphisms as all arc-preserving vertex maps, without injectivity. Their density is the number of such maps divided by the host order raised to the number of source vertices. TAS means that this density is at most one half raised to the number of source edges, for every finite tournament.

The source encodes a path with k edges by a vector in {-1,1}^k. A positive sign points from the preceding vertex to the following vertex; a negative sign points in the opposite direction. An internal vertex is a flip exactly when its two adjacent signs have product -1.

The definition of f in Section 1, repeated in Section 6, is:

> For an integer k ≥ 1, let f(k) denote the maximal m in {0,1,…,k} such that every orientation of the k-edge path with fewer than m direction flips is tournament anti-Sidorenko.

Question 6.1 in Section 6 asks:

> Does the limit of f(k)/k exist as k → ∞?

The subsequent problem asks for the exact liminf. Existence of a limit does not supply its numerical value. The source's lower bound 1/1665 is a separate result and is not needed for the finite-defect convergence argument.

The formal source correspondence uses integer sign vectors, counts internal indices by the product condition, and counts all arc-preserving maps into arbitrary finite nonempty host types. A proved sign-vector equivalence and host-reindexing bijection connect these definitions to the list-based transfer construction. No restriction on flip placement or on the size of a witnessing host is imposed. Literature completeness and global priority are not asserted.
