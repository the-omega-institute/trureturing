---
bibkey: jianu2025dycktype
authors: Marilena Jianu and Leonard Dăuş
year: 2025
title: "The number of Dyck-type lattice paths and related sequences"
doi: null
url: https://dmi.utcb.ro/wp-content/uploads/2025/09/proceeeings2025.pdf
claim: "Theorem 2.1: the number n_{i,j} of Dyck-type lattice paths (steps (1,1) and (1,-1), never below the x-axis) of length j starting at (0, i) is the sum of binomial(j, k) for k from floor((j-i)/2) to floor((j+i)/2), for all i, j >= 0; the proof is by induction on j from the recursion (2.1) n_{i,j} = n_{i-1,j-1} + n_{i+1,j-1} for i >= 1 and n_{0,j} = n_{1,j-1}."
strata_touched:
  - D5/S3/StatisticalMechanics/RandomWalks/SurvivingWalkRecurrence
license: citation-only
triage: anchor
---

# Jianu and Dăuş 2025, Dyck-type lattice paths

M. Jianu and L. Dăuş, "The number of Dyck-type lattice paths and related
sequences", Proceedings of the 22nd Workshop on Mathematics, Computer Science
and Technical Education, Technical University of Civil Engineering Bucharest,
Vol. 8 (2025), pp. 37–44. OEIS A026023 links it for its closed form.

A Dyck-type lattice path has steps `(1, 1)` and `(1, −1)`, starts on the
y-axis and never passes below the x-axis. With `n_{i,j}` the number of those
of length `j` starting at `(0, i)`, the recursion (2.1) reads
`n_{i,j} = n_{i−1,j−1} + n_{i+1,j−1}` for `i ≥ 1` and `n_{0,j} = n_{1,j−1}`,
and Theorem 2.1 states

> n_{i,j} = Σ_{k=⌊(j−i)/2⌋}^{⌊(j+i)/2⌋} C(j, k), for all i, j ≥ 0,

proved by induction on `j`. Remark 2.2 identifies these paths with random
walks on the infinite path graph started at node `i`. The row `i = 3` of its
Table 1 is `1, 2, 4, 8, 15, 30, 56, 112, 210, 420`, the start of A026023.

## Verified locator

- URL: https://dmi.utcb.ro/wp-content/uploads/2025/09/proceeeings2025.pdf
  (proceedings volume, 5,334,753 bytes, HTTP 200 on 2026-09-27; the paper is
  on printed pages 37–44, Theorem 2.1 on page 38 and Table 1 on page 39).
