---
bibkey: aliabadizerbib2024matroidmatching
authors: Mohsen Aliabadi; Shira Zerbib
year: 2024
title: Matchings in matroids over abelian groups
doi: 10.1007/s10801-024-01308-z
url: https://arxiv.org/abs/2202.07719v3
claim: "Question 2.7 asks whether a matroid is matched to a sparse paving matroid of the same rank over a torsion-free abelian group when the ground sizes are equal or differ by one."
strata_touched:
  - D5/S3/Combinatorics/Matroids/AliabadiZerbibMatroidMatching
license: citation-only
triage: anchor
---

# Aliabadi–Zerbib: matroid matchings

## Verified locator

DOI: https://doi.org/10.1007/s10801-024-01308-z

Source: https://arxiv.org/abs/2202.07719v3

The source is arXiv v3, 13 February 2024. The accessed journal text retains Question 2.7 and Definition 1.3.

## Source definitions

Page 2: “A matroid M = (E, I) of rank n is said to be a paving matroid if every (n − 1)-subset of E is independent. If M and M* are both paving matroids then M is called a sparse paving matroid.”

Page 2, Definition 1.3(1): “Let M and N be two matroids over G with r(M) = r(N) = n > 0. Let M = {a₁, . . . , aₙ} and N = {b₁, . . . , bₙ} be ordered bases of M and N, respectively. We say M is matched to N if aᵢ + bᵢ ∉ E(M), for all 1 ≤ i ≤ n.”

Page 2, Definition 1.3(2): “We say that M is matched to N if for every basis M of M there exists a basis N of N, so that M is matched to N.”

## Question 2.7

Page 5: “Let G be an abelian torsion-free group. Let M be a matroid over G and N be a sparse paving matroid over G, both of the same rank n, so that |E(M)| = |E(N)| − 1 or |E(M)| = |E(N)|. If 0 ∉ E(N), is M matched to N?”

The Lean proposition is the positive answer, using the source's standing finite, loopless setting and positive rank. Matroids, bases, independence, duals and rank use Mathlib. Paving means that X.encard + 1 equals the rank only for independent ground subsets X. An ordered basis is an injective Fin n enumeration; matching excludes sums from E(M), rather than E(N). The cardinality alternative is written |E(M)| + 1 = |E(N)| or equality.

The repository refutation uses the equal-cardinality case over ℤ. For n, s ≥ 2, delete the base {s + 1, …, s + n} from the uniform rank-n basis family on {1, …, n + s}. Both this matroid and its dual are paving. Any matching of {1, …, n} has all its targets in the deleted base, so its target range cannot be a base. No separate uniform-source or finite-cyclic-group result is asserted by the Lean settlement.

The broader tightening construction is known; apnelson1/Matroid provides Matroid.tighten and Matroid.finiteRankSparsePavingOn at revision 8ece6307a54854484c9b5fa40b9ed3c5ccc8e42b. The delivered private finite construction uses the pinned Mathlib basis constructor.

Literature completeness is ASSUMED-UNVERIFIED. The accessed journal text, sequels arXiv:2412.04516v4 and arXiv:2509.14339v2, and screened citing works contained no located settlement; this bounded screen is not an exhaustive literature claim.
