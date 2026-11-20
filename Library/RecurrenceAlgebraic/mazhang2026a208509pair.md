---
bibkey: mazhang2026a208509pair
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Extensions of Knuth's coefficient families (1993), with corrected OEIS links: Werner's conjecture in OEIS A208509, Formula, revision 28"
doi: 10.5281/zenodo.24211281
url: https://zenodo.org/records/24211281
claim: "Theorem 1: for the polynomial pair u_1 = v_1 = 1, u_{n+1} = u_n + x v_n, v_{n+1} = u_n + v_n + 1, for every n >= 1 and k >= 0, [x^k] v_n = C(n-1, 2k+1) + C(n, 2k+1) and [x^k] u_n = C(n-1, 2k) + C(n, 2k) - 1_{k=0}; in particular deg v_n = floor((n-1)/2) and deg u_n = floor(n/2). Corollary 2: with P_0 = 1, P_1 = 3 + x, P_m = (x+2) P_{m-1} - P_{m-2}, [x^k] P_m = b_{m+k+1,k} = C(m+k, 2k) + 2 C(m+k, 2k+1) for 0 <= k <= m, where b_{n,k} = [x^k] v_n. Corollary 3: for invertible z, z^(2m+1) - z^(-(2m+1)) = (z - z^-1) P_m((z - z^-1)^2); P_m(1) = L_{2m+1}; F_{(2m+1)n} = sum_{k=0}^{m} [x^k]P_m (-1)^((m+k)n) 5^k F_n^(2k+1) for n >= 0; the values P_m(-1) repeat 1, 2, 1, -1, -2, -1; and P_m(x) = prod_{j=1}^{m} (x + 4 sin^2(j pi/(2m+1))) for m >= 1. Corollary 4: in Z[x][[z]], sum_{n>=1} v_n(x) z^(n-1) = (1+z)/(1-2z+(1-x)z^2); for every k >= 0, sum_{n>=1} ([x^k] v_n) z^(n-1) = z^(2k)(1+z)/(1-z)^(2k+2); for k >= 1, sum_{n>=1} ([x^k] u_n) z^(n-1) = z^(2k-1)(1+z)/(1-z)^(2k+1); the constant column of u_n has generating function 1/(1-z). Corollary 5: for n >= 2, v_n(1) = 3 * 2^(n-2) and u_n(1) = 3 * 2^(n-2) - 1, whereas v_1(1) = u_1(1) = 1; with w_n = v_n(-1), sum_{n>=1} w_n z^(n-1) = (1+z)/(1-2z+2z^2), w_{n+2} = 2 w_{n+1} - 2 w_n, w_1 = 1, w_2 = 3. Corollary 6: for d >= 2 and m >= 0, with h_d(m) = [z^m](1+z)/(1-z)^d, h_d(m) = C(m+d-1, d-1) + C(m+d-2, d-1) = 2 C(m+d-1, d-1) - C(m+d-2, d-2) = (2m+d-1)/(d-1) C(m+d-2, d-2); h_{d+1}(m) = sum_{j=0}^{m} h_d(j); h_d(m) = sum_{j=1}^{d} (-1)^(j+1) C(d,j) h_d(m-j) for m >= d; as a polynomial in m, h_d has degree d-1, leading coefficient 2/(d-1)! and symmetry h_d(-m-d+1) = (-1)^(d-1) h_d(m)."
strata_touched:
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialCoefficients
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairDegrees
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairRowSums
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairColumnSeries
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceShear
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairMorganVoyceIdentities
  - D5/S1/Recurrence/Invariants/AffinePolynomialPairBinomialColumnFamily
license: CC-BY-4.0
triage: anchor
---

# Coefficients, degrees and row sums of the A208508/A208509 polynomial pair

## Verified locator

Zenodo record: https://zenodo.org/records/24211281

DOI: 10.5281/zenodo.24211281 (version 2; Zenodo publication date 2026-11-14, PDF dated
November 5, 2026; concept DOI 10.5281/zenodo.24211280). Source PDF:
https://zenodo.org/api/records/24211281/files/note-v2.pdf/content (text extracted locally with
layout preserved, 35,862 characters). Theorem 1 and Corollaries 2 and 3 are in Section 1; Corollaries 4 and 5 are in Section 2;
Corollary 6 is in Section 3.

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

> Corollary 2 (Morgan–Voyce shear). Let P_0(x) = 1, P_1(x) = 3 + x and P_m = (x + 2)P_{m−1} −
> P_{m−2} for m ≥ 2. Then [x^k]P_m = b_{m+k+1,k} = C(m + k, 2k) + 2 C(m + k, 2k + 1) (0 ≤ k ≤ m).
> These are André-Jeannin's r = 2 coefficient theorem (1994, equation (9)) and the array
> A111125 [13, 15].

> Corollary 3 (Further Morgan–Voyce identities). With P_m as above and z invertible,
> z^{2m+1} − z^{−(2m+1)} = (z − z^{−1}) P_m((z − z^{−1})²).
> Consequently, with the usual Fibonacci numbers F_n and Lucas numbers L_n,
> P_m(1) = L_{2m+1}, F_{(2m+1)n} = ∑_{k=0}^{m} [x^k]P_m(x) (−1)^{(m+k)n} 5^k F_n^{2k+1} (n ≥ 0).
> The values P_m(−1) repeat 1, 2, 1, −1, −2, −1. For m ≥ 1,
> P_m(x) = ∏_{j=1}^{m} (x + 4 sin²(jπ/(2m + 1))).
> These are established Morgan–Voyce and A111125 identities [13, 15].

> Corollary 4. In the ring Z[x][[z]],
> F(z, x) := ∑_{n≥1} v_n(x) z^{n−1} = (1 + z)/(1 − 2z + (1 − x)z²). (5)
> For every k ≥ 0, ∑_{n≥1} ([x^k] v_n) z^{n−1} = z^{2k}(1 + z)/(1 − z)^{2k+2}. (6)
> For k ≥ 1, the companion column generating function is
> ∑_{n≥1} ([x^k] u_n) z^{n−1} = z^{2k−1}(1 + z)/(1 − z)^{2k+1}, (7)
> and the constant column of u_n has generating function 1/(1 − z).

> Proof. Subtracting two consecutive equations for v and using the equation for u gives
> v_{n+2} = 2v_{n+1} + (x − 1)v_n (n ≥ 1), with v_1 = 1, v_2 = 3. Multiplying the generating
> series by 1 − 2z + (1 − x)z² leaves 1 + z, …

> Corollary 5. For n ≥ 2, v_n(1) = 3 · 2^{n−2}, u_n(1) = 3 · 2^{n−2} − 1, (8)
> whereas v_1(1) = u_1(1) = 1. If w_n = v_n(−1), then
> ∑_{n≥1} w_n z^{n−1} = (1 + z)/(1 − 2z + 2z²), w_{n+2} = 2w_{n+1} − 2w_n, w_1 = 1, w_2 = 3. (9)
> The cross-reference "Row sums, v(n, 1): A003948" in A208509 is false: the correct row sums
> are A003945 at index n − 1, beginning 1, 3, 6, 12, 24, not 1, 6, 30, 150, 750 [4].

> Put h_d(m) = [z^m](1 + z)/(1 − z)^d for d ≥ 2, m ≥ 0. Thus the nonzero v-column of degree k is
> h_{2k+2}, and the nonzero u-column of degree k ≥ 1 is h_{2k+1}.

> Corollary 6. For d ≥ 2 and m ≥ 0,
> h_d(m) = C(m + d − 1, d − 1) + C(m + d − 2, d − 1) = 2 C(m + d − 1, d − 1) − C(m + d − 2, d − 2)
> = (2m + d − 1)/(d − 1) · C(m + d − 2, d − 2). (10)
> Moreover h_{d+1}(m) = ∑_{j=0}^{m} h_d(j) and h_d(m) = ∑_{j=1}^{d} (−1)^{j+1} C(d, j) h_d(m − j) (m ≥ d).
> As a polynomial in m, h_d has degree d − 1, leading coefficient 2/(d − 1)!, and symmetry
> h_d(−m − d + 1) = (−1)^{d−1} h_d(m).

## Mathematical scope

The pair is the frozen `pair` of AffinePolynomialPairBinomialCoefficients, where stage n − 1
represents the source index n: u_n is its first component and v_n its second. Formula (2) is
Werner's conjecture in A208509 (see `werner2022a208509`); formula (3) is the companion A208508
family, with its exceptional constant term. The paper credits Knuth (1993), André-Jeannin (1994)
and Barry (2003, 2013) for the underlying binomial arrays. The A003948 correction in
Corollary 5 is OEIS documentation and is not a separate formal statement. Corollary 6 is formalized
for h_d itself, with the partial sums for every d and the recurrence for every d and m ≥ 2 (summed
up to min(d, m)); the identification of the columns of the pair with h_{2k+2} and h_{2k+1} is quoted
from the source and not formalized. In Corollaries 2 and 3,
b_{n,k} = [x^k] v_n is taken from the same pair, and every clause, including the trigonometric
factorization over the reals, is formalized.
