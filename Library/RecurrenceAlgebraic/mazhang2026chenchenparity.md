---
bibkey: mazhang2026chenchenparity
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Proof of Chen and Chen's parity-positivity conjectures: OEIS A392664–A392666, COMMENTS, and Conjecture 2 (p. 1)"
doi: 10.5281/zenodo.23957560
url: https://zenodo.org/records/23957560
claim: "Theorem 1: for every real r >= 3, T_{-r}(n,k) > 0 for every positive even n and 1 <= k <= n, and T_{-r}(n,k) < 0 for every odd n >= 3 and 1 < k < n. Lemma 2: for r >= 3, T_{-r}(n,2) > 0 whenever n >= 2 is even. Corollary 3: for integer m, every positive even row is entrywise nonnegative if and only if m <= -3 or m >= 0, and then strictly positive. Corollary 4: for every real m, S_n(m) = sum_{k=1}^{n} T_m(n,k) = prod_{j=0}^{n-2} (mj+2) with S_1(m) = 1; for even n, R_{m,n}(-1) = 0 and the odd-position and even-position sums both equal S_n(m)/2. Corollary 5: for real m <= -3 and even n >= 2, every root z of R_{m,n} satisfies L_n <= |z| <= U_n, where L_n and U_n are the least and largest of the positive ratios T_m(n,k)/T_m(n,k+1), 1 <= k < n, and L_n U_n = 1. Corollary 8: for q >= 1, R_{-1,2q}(y) = R_{-2,2q}(y) = (1-y)^{2q-2}(1+y), R_{-1,2q+1}(y) = (1-y)^{2q-2}(1+y^2) and R_{-2,2q+1}(y) = (1-y)^{2q}, so M_n(-1) = M_n(-2) = 1 for n >= 2; R_{0,n} = (1+y)^{n-1}; for m > 0 and n >= 2 every root of R_{m,n} is simple and negative; at m = -3 nonreal roots occur in row 6."
strata_touched:
  - D5/S1/Recurrence/Algebraic/ChenChenRealStepRowSums
  - D5/S1/Recurrence/Algebraic/ChenChenRealStepSigns
  - D5/S1/Recurrence/Algebraic/ChenChenIntegerStepCriterion
  - D5/S1/Recurrence/Algebraic/ChenChenRootAnnulus
  - D5/S1/Recurrence/Algebraic/ChenChenBoundarySteps
license: CC-BY-4.0
triage: anchor
---

# Signs, integer-step criterion, row sums and parity sums of the step-m Eulerian triangle

## Verified locator

Zenodo record: https://zenodo.org/records/23957560

DOI: 10.5281/zenodo.23957560 (version 2; Zenodo publication date 2026-11-04, PDF dated
3 November 2026). Source PDF:
https://zenodo.org/api/records/23957560/files/note-v2.pdf/content (text extracted locally,
24,508 characters). Theorem 1 opens the paper; Corollary 3 follows the proof of Theorem 1, and
Corollary 4 follows the reflection identity (3), Corollary 5 follows Corollary 4, and Corollary 8 is in Section 5.

## Source statement

> Theorem 1. For every real r ≥ 3, the triangle of step m = −r satisfies
> 1. T_{−r}(n, k) > 0 for every positive even n and 1 ≤ k ≤ n;
> 2. T_{−r}(n, k) < 0 for every odd n ≥ 3 and 1 < k < n.

> Lemma 2. For r ≥ 3, T_{−r}(n, 2) > 0 whenever n ≥ 2 is even.

> Corollary 3. For integer m, every positive even row is entrywise nonnegative if and only if
> m ≤ −3 or m ≥ 0. For exactly these parameters, every positive even row is in fact strictly
> positive.

> Proof. Theorem 1 covers m ≤ −3. If m ≥ 0, both coefficients in (2) are at least one, so
> induction gives strict positivity of every row. The two remaining integer parameters fail
> already at T_m(4, 2) = T_m(4, 3) = 2m² + 6m + 3 = −1 (m = −1, −2).

> Corollary 4. For every real m, S_n(m) := ∑_{k=1}^{n} T_m(n, k) = ∏_{j=0}^{n−2} (mj + 2),
> S_1(m) = 1. For even n, R_{m,n}(−1) = 0, ∑_{1≤k≤n, k odd} T_m(n, k) =
> ∑_{1≤k≤n, k even} T_m(n, k) = ½ S_n(m).

> Proof. For n ≥ 3, extend the preceding row by zeros just for summing (2). At k = 1, n, the
> same formula then gives the boundary value 1. A preceding-row entry at position j has total
> coefficient (m(n − j − 1) + 1) + (m(j − 1) + 1) = m(n − 2) + 2. …

> Corollary 5. For real m ≤ −3 and even n ≥ 2, every root z of R_{m,n} satisfies
> L_n ≤ |z| ≤ U_n, L_n = min_{1≤k<n} T_m(n, k)/T_m(n, k + 1),
> U_n = max_{1≤k<n} T_m(n, k)/T_m(n, k + 1). All these ratios are positive; symmetry also
> gives L_n U_n = 1.

> Proof. This is the Eneström–Kakeya bound [7]; … Theorem 1 supplies positive coefficients
> here. Reflection makes the set of consecutive ratios invariant under reciprocation, so
> L_n = 1/U_n.

> Corollary 8. For q ≥ 1, the two excluded integer steps satisfy
> R_{−1,2q}(y) = R_{−2,2q}(y) = (1 − y)^{2q−2}(1 + y), and
> R_{−1,2q+1}(y) = (1 − y)^{2q−2}(1 + y²), R_{−2,2q+1}(y) = (1 − y)^{2q}.
> Thus M_n(−1) = M_n(−2) = 1 for n ≥ 2; both growth exponents are zero. Also R_{0,n} = (1 + y)^{n−1}.
> For m > 0 and n ≥ 2, every root of R_{m,n} is simple and negative. At m = −3, nonreal roots occur
> already in row 6.

> Proof. The factor formulas follow from (5) in successive even–odd pairs, starting with
> R_{m,2} = 1 + y and R_{−1,3} = 1 + y², R_{−2,3} = (1 − y)². At m = 0, (5) multiplies by 1 + y at
> each step. … Finally, R_{−3,6}(y) = (y + 1)(y⁴ + 16y³ + 246y² + 16y + 1). For real y ≠ 0, the
> quartic divided by y² is (y + y⁻¹ + 8)² + 180 > 0, so its four roots are nonreal.

## Mathematical scope

T_m is Chen and Chen's step-m Eulerian triangle (see `chenchen2026stepm`): T_m(n,1) =
T_m(n,n) = 1 and the interior recursion T_m(n,k) = (m(n−k)+1)T_m(n−1,k−1) +
(m(k−1)+1)T_m(n−1,k), with R_{m,n}(y) = ∑ T_m(n,k) y^{k−1}. The row sums and even-row
alternating sums are among the adjacent COMMENTS statements of OEIS A392664–A392666; the
paper's coverage table lists them as proved by the reflection identity (3) and Corollary 4.
The parameter m is any real number in Theorem 1 and Corollary 4, not only the integer steps of
the OEIS entries; Corollary 3 restricts to integer m. Corollary 5 is the Eneström–Kakeya bound
(reference [7] of the paper) applied to the positive even rows given by Theorem 1. In Corollary 8,
M_n(m) is the largest modulus of a complex root of R_{m,n}, and the steps m = −1, −2 are the two
integer steps excluded from Corollary 3.
