---
bibkey: mazhang2026edgecollision
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Proof of Arkadeep Dutta's edge-collision ratio conjecture (OEIS A396659)"
doi: 10.5281/zenodo.23885975
url: https://zenodo.org/records/23885975
claim: "Theorem 1 (3): for every n >= 1, T(n,n+1) = n! and T(n,n^2+1) = (n!)^n, with the linear-walk normalization of OEIS A396659 revision 16."
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/CollisionEarliest
license: CC-BY-4.0
triage: anchor
---

# Edge-collision walks: the earliest collision count

## Verified locator

DOI: 10.5281/zenodo.23885975 (version 4; Zenodo record dated 2026-11-02, PDF dated
1 November 2026). Source PDF:
https://zenodo.org/api/records/23885975/files/note-v4.pdf/content (text extracted locally,
about 12,800 characters). Theorem 1 is on p. 1; the T(n, n + 1) argument closes Section 5.

## Source statement

> We count the walk in T(n, k) when its first k − 1 edges are distinct, its last edge
> repeats an earlier edge, and its vertices include all of V.

> Moreover, for every n ≥ 1, T(n, n + 1) = n!, T(n, n² + 1) = (n!)ⁿ.

> Thus x0, . . . , xn−1 is a permutation of V beginning at v; xn is any of the n vertices.
> Its unique earlier occurrence determines xn+1.

## Mathematical scope

The walks are vertex lists with a distinguished start, on the complete directed graph with
one loop at each vertex, as in OEIS A396659 revision 16 (see `dutta2026a396659`). The
formalization covers the first companion formula T(n, n + 1) = n!; the second,
T(n, n² + 1) = (n!)ⁿ, uses last-exit trees and is not covered here.
