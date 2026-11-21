---
bibkey: mazhang2026a320043squares
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "OEIS A320043, COMMENTS, revision 43: a square-value refutation extending Zhu's Pell-prime result (2011)"
doi: 10.5281/zenodo.24058057
url: https://zenodo.org/records/24058057
claim: "Corollary 6: for n >= 1 and 1 <= k <= n, with X(n,k) = (n+1-k)^2 k / gcd(n+1-k,k)^3, one has X(2m-1,m) = 1 for m >= 1, prod_{k=1}^{n} X(n,k)^(1/3) = B(n+1) with B(N) = prod_{k=1}^{N} k/gcd(k,N) (A119619), and B(p) = (p-1)! for prime p. Corollary 7: for N >= 2, with Euler's totient phi and E(m) = prod_{q | m, q prime} (1 - q), E(1) = 1, one has 12 a(N-1) = sum_{m | N} (m^3 phi(m) - m^2 E(m)), where a(n) = sum_{k=1}^{n} (n+1-k)^2 k / gcd(n+1-k,k)^3."
strata_touched:
  - D5/S3/ArithSums/SpeziaA320043RowProduct
  - D5/S3/ArithSums/SpeziaA320043AllRowDivisorFormula
  - D5/S3/ArithSums/SpeziaA320043PellPrimeIndices
license: CC-BY-4.0
triage: anchor
---

# The A320043 row product

## Verified locator

Zenodo record: https://zenodo.org/records/24058057

DOI: 10.5281/zenodo.24058057 (version 2; Zenodo publication date 2026-11-08, PDF dated
November 5, 2026). Source PDF:
https://zenodo.org/api/records/24058057/files/note-v2.pdf/content (text extracted locally,
19,673 characters). Corollary 4 is in Section 2, PDF page 3; Corollaries 6 and 7 are in
Section 3, PDF page 4.

## Source statement

> The triangle entry A322550 states a product formula added by Spezia on June 24, 2024 [2]. It
> follows directly from the same gcd reduction; it is unaffected by the square-value conjecture.

> Corollary 6. For n ≥ 1 and 1 ≤ k ≤ n, put X(n, k) = (n + 1 − k)² k/ gcd(n + 1 − k, k)³. Then
> X(2m − 1, m) = 1 for every m ≥ 1, and ∏_{k=1}^{n} X(n, k)^{1/3} = B(n + 1),
> B(N) = ∏_{k=1}^{N} k/gcd(k, N) (A119619). Moreover B(p) = (p − 1)! for prime p.

> Proof. The central entry has numerator m³ and denominator m³. For the product,
> gcd(n + 1 − k, k) = gcd(n + 1, k) …

> Corollary 7. Let N ≥ 2, let φ be Euler's totient function, and put E(m) = ∏_{q|m, q prime} (1 − q),
> with E(1) = 1. An all-row generalization of the prime-row identity is
> 12a(N − 1) = ∑_{m|N} (m³φ(m) − m²E(m)).

> Proof. Grouping by d = gcd(N, k) gives a(N − 1) = ∑_{m|N} C(m), where
> C(m) = ∑_{1≤j<m, (j,m)=1} (m − j)² j, C(1) = 0. Let U(m) = ∑_{j=1}^{m−1} (m − j)² j = m²(m² − 1)/12.
> The same grouping before division by the gcd gives U(m) = ∑_{d|m} d³ C(m/d). Möbius inversion
> yields 12C(m) = m⁴ ∑_{d|m} μ(d)/d − m² ∑_{d|m} μ(d)d = m³φ(m) − m²E(m). … Summing proves the
> formula, including the zero contribution at m = 1.

> Corollary 4. Let r_j = ((2 + √3)^j + (2 − √3)^j)/2 be A001075, with r_0 = 1, r_1 = 2. For a
> prime p, a(p − 1) is a square if and only if p is a prime term of (r_j), that is, a term of
> A277434. If p > 2, then p = x_{2^h} for some h ≥ 0, and p ≡ 7 (mod 30).

> Proof. Since (2 + √3)² = 7 + 2√12, r_{2t} = x_t. … For odd d > 1, write (7 + 2√12)^s = u + v√12.
> … hence x_s | x_{ds}. Since 1 < x_s < x_{ds}, a prime x_t requires t = 2^h. The doubling
> identity x_{2t} = 2x_t² − 1 and x_1 = 7 then give x_{2^h} ≡ 7 (mod 30) by induction. The index
> restriction was proved by Zhu (2011) [3, p. 200]. The congruence and divisibility also appear in
> Tiffin's 2016 comments in A001075 and A277434 [7, 9]; Andrews gave the odd-multiple argument
> for the subsequence r_{4j} in 2019 [12].

## Mathematical scope

X(n, k) is the n-th antidiagonal of Spezia's triangle A322550 (see `spezia2018a320043`), whose
row sums are A320043. B is OEIS A119619 (M. Fuller, 2006); the prime value B(p) = (p − 1)! is
Steinerberger's 2006 comment there. The paper's attribution table marks the product formula as
"Reproved; prior formula Spezia (2024)", so the identity is literature-attested; the note
supplies a proof by the gcd reduction gcd(n + 1 − k, k) = gcd(n + 1, k).

For Corollary 7, a(n) is the A320043 row sum of the frozen SpeziaA320043SquareValuesRefutation
module. The paper credits the generalization to Ma and Zhang. Its proof uses Möbius inversion
with the divisor sums ∑_{d|m} μ(d)/d = φ(m)/m and ∑_{d|m} μ(d)d = E(m).

SpeziaA320043PellPrimeIndices.result states Corollary 4 with r defined by its recurrence and
x_0 = 1, x_1 = 7, x_{t+2} = 14x_{t+1} − x_t: the quotients of a are exact, r_{2t} = x_t, a prime p
has a(p − 1) a square iff p is a term of r, for p > 2 iff p = x_{2^h} for some h, and every
x_{2^h} is 7 modulo 30. The index restriction is Zhu's (2011); the congruence and divisibility
appear in Tiffin's 2016 OEIS comments; the paper credits the odd-multiple argument to Andrews
(2019).
