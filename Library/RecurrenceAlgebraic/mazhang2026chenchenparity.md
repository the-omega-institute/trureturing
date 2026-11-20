---
bibkey: mazhang2026chenchenparity
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Proof of Chen and Chen's parity-positivity conjectures: OEIS A392664–A392666, COMMENTS, and Conjecture 2 (p. 1)"
doi: 10.5281/zenodo.23957560
url: https://zenodo.org/records/23957560
claim: "Corollary 4: for every real m, S_n(m) = sum_{k=1}^{n} T_m(n,k) = prod_{j=0}^{n-2} (mj+2) with S_1(m) = 1; for even n, R_{m,n}(-1) = 0 and the odd-position and even-position sums both equal S_n(m)/2."
strata_touched:
  - D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums
license: CC-BY-4.0
triage: anchor
---

# Row sums and even-row parity sums of the step-m Eulerian triangle

## Verified locator

DOI: 10.5281/zenodo.23957560 (version 2; Zenodo publication date 2026-11-04, PDF dated
3 November 2026). Source PDF:
https://zenodo.org/api/records/23957560/files/note-v2.pdf/content (text extracted locally,
24,508 characters). Corollary 4 follows the reflection identity (3).

## Source statement

> Corollary 4. For every real m, S_n(m) := ∑_{k=1}^{n} T_m(n, k) = ∏_{j=0}^{n−2} (mj + 2),
> S_1(m) = 1. For even n, R_{m,n}(−1) = 0, ∑_{1≤k≤n, k odd} T_m(n, k) =
> ∑_{1≤k≤n, k even} T_m(n, k) = ½ S_n(m).

> Proof. For n ≥ 3, extend the preceding row by zeros just for summing (2). At k = 1, n, the
> same formula then gives the boundary value 1. A preceding-row entry at position j has total
> coefficient (m(n − j − 1) + 1) + (m(j − 1) + 1) = m(n − 2) + 2.

## Mathematical scope

T_m is Chen and Chen's step-m Eulerian triangle (see `chenchen2026stepm`): T_m(n,1) =
T_m(n,n) = 1 and the interior recursion T_m(n,k) = (m(n−k)+1)T_m(n−1,k−1) +
(m(k−1)+1)T_m(n−1,k), with R_{m,n}(y) = ∑ T_m(n,k) y^{k−1}. The row sums and even-row
alternating sums are among the adjacent COMMENTS statements of OEIS A392664–A392666; the
paper's coverage table lists them as proved by the reflection identity (3) and Corollary 4.
The parameter m is any real number here, not only the integer steps of the OEIS entries.
