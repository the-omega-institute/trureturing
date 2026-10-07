---
bibkey: egecioglu2026rotations
authors: Ömer Eğecioğlu, Collier Gaiser, Mei Yin
year: 2026
title: "Pattern avoidance in permutations and their rotations"
doi: 10.48550/arXiv.2607.20750
url: https://arxiv.org/abs/2607.20750v1
claim: "Exact counts of permutations whose first k rotations avoid a pattern of length three, and Open Question 6.1 on the Wilf classes of rotation avoidance for patterns of length four."
strata_touched:
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceDefs
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceSymmetry
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCircular
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidance
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending
  - D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration
license: citation-only
triage: anchor
---

# Eğecioğlu, Gaiser and Yin, pattern avoidance in permutations and their rotations

The i-th rotation of a permutation p_1 ⋯ p_n is p_i ⋯ p_n p_1 ⋯ p_{i−1}. For a pattern q, S_n^{(k)}(q) is the
set of permutations of [n] whose first k rotations all avoid q. The paper gives exact formulas for
|S_n^{(k)}(q)| for every k ≥ 2 and every pattern q of length three, and observes that the resulting
Wilf-equivalence classes are exactly the orbits under complement and reverse.

Section 6, Open Question 6.1, asks whether the same holds for patterns of length four: for every k ≥ 4, are the
Wilf-equivalence classes of S_n^{(k)}(q), q ∈ S_4, exactly the eight complement–reverse orbits?

The modules listed above formalize the statement and the first part of an answer: complement–reverse orbits
are Wilf-equivalent for every k, the circular reductions of the counts for k = n − 1 and k = n, and exact counts
of the linear classes that arise after cutting at an extreme value (2^{n−1}, 2^n − n, F_{2n−1} and the
ascending class).

## Verified locator

DOI: 10.48550/arXiv.2607.20750

URL: https://arxiv.org/abs/2607.20750v1

- Locator: Section 6, Open Question 6.1, Wilf classes of S_n^{(k)}(q) for q of length four.
