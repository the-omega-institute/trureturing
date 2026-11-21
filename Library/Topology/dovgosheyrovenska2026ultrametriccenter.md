---
bibkey: dovgosheyrovenska2026ultrametriccenter
authors: Oleksiy Dovgoshey and Olga Rovenska
year: 2026
title: On the center of distances of finite ultrametric spaces
doi: 10.48550/arXiv.2603.25850
url: https://arxiv.org/abs/2603.25850v1
claim: "Corollary 3.12: a finite ultrametric space with |C(X)| = m >= 1 has at least 2^(m-1) points; Example 3.13 attains this with binary words; Conjecture 4.4 (proved as Corollary 4.6 of arXiv:2609.11384): every finite A in R+ with 0 in A is D(X) = C(X) for a finite ultrametric space."
strata_touched:
  - D5/S3/Combinatorics/Geometry/UltrametricCenterMinimumOrder
license: citation-only
triage: anchor
---

# Minimum order of finite ultrametric spaces with a prescribed center of distances

## Verified locator

DOI: 10.48550/arXiv.2603.25850

Source: https://arxiv.org/abs/2603.25850v1. Corollary 3.12 and Example 3.13 are in Section 3;
Conjecture 4.4 is in Section 4.

The conjecture is proved in O. Dovgoshey, N. S. Jaiswal, S. P. S. Kainth, G. Kaur and
O. Rovenska, "Maximal Center of Distances of Finite Ultrametric Spaces and Perfect Binary Trees",
arXiv:2609.11384v1, https://arxiv.org/abs/2609.11384v1, Proposition 4.5 and Corollary 4.6; its
Remark 4.7 records that Corollary 4.6 is Conjecture 4.4.

## Source statements

> Corollary 3.12 Let m ≥ 1 be an integer number and let (X, d) be a finite ultrametric space such
> that |C(X)| = m, where C(X) is the center of distances of the space (X, d). Then the set X
> contains at least 2^(m−1) points, |X| ≥ 2^(m−1).

> Example 3.13 Let n ≥ 1 be an integer number and let X be the set of all finite binary words
> (x₁, …, xₙ), where xᵢ ∈ {0, 1} for each i ∈ {1, …, n}. Then the cardinal number of X is 2ⁿ,
> |X| = 2ⁿ. Let us define the distance between words x = (x₁, …, xₙ) and y = (y₁, …, yₙ) as
> d(x, y) := 2^(−m) if m is the first place at which the words x and y are different, and write
> d(x, y) := 0 if x = y. Then (X, d) is an ultrametric space with the center of distances
> C(X) = {0} ∪ {1/2, …, 1/2ⁿ}.

> Conjecture 4.4 Let A be a finite subset of R⁺ such that 0 ∈ A. Then there exists a finite
> ultrametric space (X, d) that satisfies the equalities D(X) = C(X) = A, where D(X) and C(X) are
> the distance set of (X, d) and, respectively, the center of distances of (X, d).

> Proposition 4.5 (arXiv:2609.11384). Let A be a finite subset of R⁺ and let 0 ∈ A. Then, up to
> isometry, there exists a unique ultrametric space (X, d) ∈ MCD such that D(X) = C(X) = A.

## Mathematical scope

UltrametricCenterMinimumOrder.lower_bound is Corollary 3.12 together with the attainment of
Example 3.13: every finite ultrametric space with |C(X)| = k ≥ 1 has at least 2^(k−1) points,
and for every k ≥ 1 some finite ultrametric space has |C(X)| = k and exactly 2^(k−1) points. The
proof splits the space at its diameter m: the open m-balls around two points at distance m are
disjoint, and the center of each contains C(X) \ {m}, so induction on the order applies.

UltrametricCenterMinimumOrder.result is Conjecture 4.4 with the minimum order. For a finite set A
of reals, being C(X) for some finite ultrametric space, being D(X) = C(X) for some finite
ultrametric space, and 0 ∈ A ⊆ [0, ∞) are equivalent; for such A, the least order of a finite ultrametric space with C(X) = A is 2^(|A|−1), attained by a space
with D(X) = C(X) = A. The realization uses binary words of length |A| − 1, with the distance of two
words the element of A indexed by one plus the highest position where they differ. It replaces the
labelled perfect binary tree of Proposition 4.5 by this explicit word metric; the uniqueness up to
isometry in Proposition 4.5 is not formalized.
