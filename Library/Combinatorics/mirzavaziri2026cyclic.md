---
bibkey: mirzavaziri2026cyclic
authors: Madjid Mirzavaziri, Daniel Yaqubi
year: 2026
title: "Cyclic Latin Eulerian Numbers"
doi: 10.48550/arXiv.2609.28808
url: https://arxiv.org/abs/2609.28808v1
claim: "computations for n ≤ 5 (Table 1) reveal a surprising fact: ⟨⟨n k⟩⟩_c is actually invariant under the full symmetric group action on k … Identifying the hidden mechanism behind this full invariance remains an open problem."
strata_touched:
  - D5/S3/Combinatorics/CyclicLatinEulerianRefutation
license: citation-only
triage: anchor
---

# Mirzavaziri and Yaqubi, cyclic Latin Eulerian numbers

The paper restricts the Latin Eulerian refinement to the row-reordered cyclic squares `L_π`, whose rows are the rows of
`C(i, j) = (i + j) mod n` taken in the order `π`, and counts permutations by the vector of column-ascent numbers.

## Verified locator

DOI: 10.48550/arXiv.2609.28808

URL: https://arxiv.org/abs/2609.28808v1

The arXiv record shows only v1 (23 September 2026).

- Locator: Definition 2.1, `⟨⟨n k⟩⟩_c := #{π ∈ S_n : k_j(L_π) = k_j for all 1 ≤ j ≤ n}`, where `k_j(L_π)` is the number of ascents in
  column `j` of `L_π`.
- Locator: Remark 3.9, "Cyclically shifting π naturally explains an order-n cyclic symmetry for ⟨⟨n k⟩⟩_c. However, computations for
  n ≤ 5 (Table 1) reveal a surprising fact: ⟨⟨n k⟩⟩_c is actually invariant under the full symmetric group action on k … Identifying the
  hidden mechanism behind this full invariance remains an open problem."
- Locator: Table 1 lists one value per multiset, for example 2 for the multiset {1, 1, 2, 2} at n = 4.

## Reading of the statement

The asserted invariance says `⟨⟨n k∘σ⟩⟩_c = ⟨⟨n k⟩⟩_c` for every vector `k` and every permutation `σ` of the column positions.

## Scope of the recorded answer

The invariance fails for every `n ≥ 4`. Column `c` of `L_π` ascends exactly where the word `(π_i + c) mod n` ascends, and one cyclic shift
of the values changes only the two comparisons next to the value that wraps from `n − 1` to `0`. Consequently consecutive column-ascent
numbers differ by at most one, a change happens at most at the two shifts where the wrapping value sits at the first or at the last row,
and every attained vector takes two adjacent values whose larger value occupies one cyclic interval of columns. At `n = 4` the vector
`(1, 1, 2, 2)` is attained by two permutations while `(1, 2, 1, 2)` is attained by none. Only the cyclic symmetry holds.

## Bounded prior-resolution evidence

Read on 2026-09-26: the arXiv record (v1 only); the authors' earlier paper arXiv:2609.25100 does not address Remark 3.9. This is a bounded
negative finding for a three-day-old paper.
