---
bibkey: mazhang2026a208509pair
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28"
doi: 10.5281/zenodo.24211281
url: https://zenodo.org/records/24211281
claim: "Theorem 1: for the polynomial pair u_1 = v_1 = 1, u_{n+1} = u_n + x v_n, v_{n+1} = u_n + v_n + 1, for every n >= 1 and k >= 0, [x^k] v_n = C(n-1, 2k+1) + C(n, 2k+1) and [x^k] u_n = C(n-1, 2k) + C(n, 2k) - 1_{k=0}; in particular deg v_n = floor((n-1)/2) and deg u_n = floor(n/2). Corollary 5: for n >= 2, v_n(1) = 3 * 2^(n-2) and u_n(1) = 3 * 2^(n-2) - 1, whereas v_1(1) = u_1(1) = 1; with w_n = v_n(-1), sum_{n>=1} w_n z^(n-1) = (1+z)/(1-2z+2z^2), w_{n+2} = 2 w_{n+1} - 2 w_n, w_1 = 1, w_2 = 3."
strata_touched:
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairDegrees
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums
license: CC-BY-4.0
triage: anchor
---

# Coefficients, degrees and row sums of the A208508/A208509 polynomial pair

## Verified locator

Zenodo record: https://zenodo.org/records/24211281

DOI: 10.5281/zenodo.24211281 (version 2; Zenodo publication date 2026-11-14, PDF dated
November 5, 2026; concept DOI 10.5281/zenodo.24211280). Source PDF:
https://zenodo.org/api/records/24211281/files/note-v2.pdf/content (text extracted locally with
layout preserved, 35,862 characters). Theorem 1 is in Section 1; Corollary 5 is in Section 2.

## Source statement

> Clark Kimberling's entries A208508 and A208509 define polynomials in Z[x] by u_1 = v_1 = 1
> and, for n ≥ 1, u_{n+1} = u_n + x v_n, v_{n+1} = u_n + v_n + 1. (1)

> Theorem 1. For every n ≥ 1 and k ≥ 0,
> [x^k] v_n = C(n − 1, 2k + 1) + C(n, 2k + 1), (2)
> [x^k] u_n = C(n − 1, 2k) + C(n, 2k) − 1_{k=0}. (3)
> These identities include every coefficient beyond the degrees of the polynomials. In
> particular, deg v_n = ⌊(n − 1)/2⌋ and deg u_n = ⌊n/2⌋.

> Proof. Write a_{n,k} = [x^k] u_n and b_{n,k} = [x^k] v_n, with b_{n,−1} = 0. Taking
> coefficients in (1) gives a_{n+1,k} = a_{n,k} + b_{n,k−1}, b_{n+1,k} = a_{n,k} + b_{n,k} + 1_{k=0}.
> …

> Corollary 5. For n ≥ 2, v_n(1) = 3 · 2^{n−2}, u_n(1) = 3 · 2^{n−2} − 1, (8)
> whereas v_1(1) = u_1(1) = 1. If w_n = v_n(−1), then
> ∑_{n≥1} w_n z^{n−1} = (1 + z)/(1 − 2z + 2z²), w_{n+2} = 2w_{n+1} − 2w_n, w_1 = 1, w_2 = 3. (9)
> The cross-reference "Row sums, v(n, 1): A003948" in A208509 is false: the correct row sums
> are A003945 at index n − 1, beginning 1, 3, 6, 12, 24, not 1, 6, 30, 150, 750 [4].

## Mathematical scope

The pair is the frozen `pair` of AffinePolynomialPairBinomialCoefficients, where stage n − 1
represents the source index n: u_n is its first component and v_n its second. Formula (2) is
Werner's conjecture in A208509 (see `werner2022a208509`); formula (3) is the companion A208508
family, with its exceptional constant term. The paper credits Knuth (1993), André-Jeannin (1994)
and Barry (2003, 2013) for the underlying binomial arrays. The A003948 correction in
Corollary 5 is OEIS documentation and is not a separate formal statement.
