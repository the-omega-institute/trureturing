---
bibkey: mazhang2026hermitesignedmode
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Resolving the Hermite coefficient conjectures in OEIS A381423, Comments (revision 8)"
doi: 10.5281/zenodo.23957586
url: https://zenodo.org/records/23957586
claim: "Theorem 1: for every n >= 0, the largest signed coefficient of the physicists' Hermite polynomial H_n is unique, and q(n) = floor((2n + 7 - sqrt(8n + 21))/8), a(n) = n - 4q(n); equivalently a(n) is the least nonnegative integer j congruent to n mod 4 with j^2 + 7j + 7 >= 2n; moreover a(n+1) - a(n) is 1 or -3. Corollary 2: the difference sequence is a concatenation of (1,1,1,-3) and (1,1,1,1,-3), the first block of length five; with R_j = floor((j^2 + 5j + 7)/8) for j >= 1, apart from the first block the length-five blocks have precisely the block indices r = R_j, the block indexed by r starting at difference index n_r, with starting indices 4R_j + j; between the length-five blocks indexed by R_j and R_{j+1} there are exactly R_{j+1} - R_j - 1 = j/4 + O(1) length-four blocks; alpha_n <= a(n) < alpha_n + 4, a(n) = sqrt(2n) + O(1) and a(n)/sqrt(2n) -> 1, where alpha_n = (sqrt(8n + 21) - 7)/2. Theorem 3: the least exponent b(n) of a largest absolute coefficient is the least nonnegative j congruent to n mod 2 with j^2 + 5j + 2 >= 2n; b(n+1) - b(n) is 1 or -1; there are two absolute maxima exactly at the degrees N_m = 2m(m+2) + (m+1)(-1)^(m+1), m >= 1, in increasing order, and one absolute maximum at every other degree. Corollary 4: for every n >= 0, t(n) = floor((2n + 5 - sqrt(8n + 17))/4), b(n) = n - 2t(n), b(n) = sqrt(2n) + O(1); the absolute-mode difference sequence consists of (1,-1) and (1,1,-1), its initial block has length three, and apart from that block its length-three blocks have indices L_j = floor((j+1)(j+2)/4), j >= 1, starting at difference indices 2L_j + j; at every degree with two absolute maxima the maximizing exponents are b(n) and b(n)+2, their coefficients have opposite signs, and B(n) = M(n); B(n) = M(n) if and only if there are two absolute maxima or t(n) is even; and a(n) is in {b(n)-2, b(n), b(n)+2} for every n >= 0."
strata_touched:
  - D5/S3/Analytic/Polynomial/HermiteSignedModeThreshold
  - D5/S3/Analytic/Polynomial/HermiteSignedModeBlocks
  - D5/S3/Analytic/Polynomial/HermiteAbsoluteModeBlocks
license: CC-BY-4.0
triage: anchor
---

# Unique signed Hermite mode and its quadratic threshold

## Verified locator

Zenodo record: https://zenodo.org/records/23957586

DOI: 10.5281/zenodo.23957586 (version 3; Zenodo publication date 2026-11-04, PDF dated
3 November 2026; concept DOI 10.5281/zenodo.23957585). Source PDF:
https://zenodo.org/api/records/23957586/files/note-v3.pdf/content (text extracted locally with
layout preserved, 20,124 characters). Theorem 1 is in Section 1; Corollary 2 is in Section 2; Theorem 3 and Corollary 4 are in Section 3.

## Source statement

> Write a(n) for the least j ∈ {0, . . . , n} at which [x^j]H_n(x) is maximal, comparing signed
> coefficients.

> Theorem 1. For every n ≥ 0, the largest signed coefficient of H_n is unique, and
> q(n) = ⌊(2n + 7 − √(8n + 21))/8⌋, a(n) = n − 4q(n). (2)
> Equivalently, a(n) is the least nonnegative integer j ≡ n (mod 4) such that
> F(j) := j² + 7j + 7 ≥ 2n. (3)
> Moreover, a(n + 1) − a(n) ∈ {1, −3} for every n ≥ 0.

> Set n_0 = 0. For r ≥ 1 define j_r = min{j ≥ 0 : j² + 5j + 7 ≥ 8r}, n_r = 4r + j_r. (7)

> Corollary 2. The difference sequence is a concatenation of (1, 1, 1, −3) and (1, 1, 1, 1, −3). The
> first block has length five. For j ≥ 1, let R_j = ⌊(j² + 5j + 7)/8⌋. (8)
> Apart from the first block, the blocks of length five have precisely the block indices r = R_j, where
> the block indexed by r starts at difference index n_r. Their starting indices are 4R_j + j. Between
> the length-five blocks indexed by R_j and R_{j+1} there are exactly R_{j+1} − R_j − 1 = j/4 + O(1)
> length-four blocks. Furthermore, α_n ≤ a(n) < α_n + 4, a(n) = √(2n) + O(1), lim a(n)/√(2n) = 1. (9)

> Theorem 3. The integer b(n) is the least nonnegative j ≡ n (mod 2) satisfying
> j² + 5j + 2 ≥ 2n. (10)
> For every n ≥ 0, b(n + 1) − b(n) ∈ {1, −1}. There are two absolute maxima exactly at the degrees
> N_m = 2m(m + 2) + (m + 1)(−1)^{m+1}, m ≥ 1, (11)
> in increasing order. At every other degree there is one absolute maximum.

> Corollary 4. For every n ≥ 0, t(n) = ⌊(2n + 5 − √(8n + 17))/4⌋, b(n) = n − 2t(n), b(n) = √(2n) + O(1).
> The absolute-mode difference sequence consists of (1, −1) and (1, 1, −1). Its initial block has
> length three. Apart from that initial block, its length-three blocks have indices
> L_j = ⌊(j + 1)(j + 2)/4⌋, j ≥ 1, and start at difference indices 2L_j + j. At every degree with
> two absolute maxima the two maximizing exponents are b(n) and b(n) + 2, their coefficients have
> opposite signs, and B(n) = M(n). More generally, B(n) = M(n) if and only if either there are two
> absolute maxima or t(n) is even. The signed and absolute modes interlace in the precise sense
> a(n) ∈ {b(n) − 2, b(n), b(n) + 2} for every n ≥ 0.

## Mathematical scope

H_n uses the physicists' normalization of DLMF 18.5.13, as in the frozen HermiteSignedMode
module, whose result already gives the least maximizer a(n) and the differences 1 and −3. The
remaining clauses are formalized: every other exponent, including those above n, has a strictly
smaller coefficient; among j ≡ n (mod 4), a(n) ≤ j exactly when F(j) ≥ 2n, so a(n) is the least
such j; and a(n) = n − 4q(n) with the
radical floor formula over the reals. For Corollary 2, n_r = 4r + j_r for every r (j_0 = 0 gives
n_0 = 0), and q(n) ≥ r exactly when n ≥ n_r. The block description is formalized as: a(n + 1) − a(n)
= −3 exactly when n + 1 is some n_r, the other differences being 1 by the frozen difference result;
n_1 = 5; n_{r+1} − n_r ∈ {4, 5}; the gap is five exactly when r = R_j for some j ≥ 0 (R_0 = 0 is the
first block), and n_{R_j} = 4R_j + j; blocks strictly between R_j and R_{j+1} have length four. The
O(1) terms are made explicit and sharpened: −3/4 ≤ R_{j+1} − R_j − 1 − j/4 ≤ 1/4, both ends occurring by
direct computation (j = 7 and j = 3), and −7/2 < a(n) − √(2n) < 3.
For Theorem 3, the frozen HermiteAbsoluteMode result gives the least maximizer b(n) and the
differences ±1, and the frozen HermiteAbsoluteTieOrders result enumerates the degrees with exactly
two maxima as N_m. The remaining clauses are formalized together with Corollary 4: among j ≡ n (mod 2),
b(n) ≤ j exactly when j² + 5j + 2 ≥ 2n; every degree has a unique absolute maximum or exactly two;
and the maximum is unique exactly at the degrees that are not of the form N_m. For Corollary 4, the
O(1) term is made explicit as −5/2 < b(n) − √(2n) < 2; the blocks are described through
m_k = 2k + h_k (m_0 = 0, m_1 = 3), with b(n + 1) − b(n) = −1 exactly when n + 1 is some m_k, gaps
m_{k+1} − m_k ∈ {2, 3}, gap three exactly when k = L_j for some j ≥ 0 (L_0 = 0 is the initial
block), m_{L_j} = 2L_j + j, and gap two strictly between consecutive L_j.
