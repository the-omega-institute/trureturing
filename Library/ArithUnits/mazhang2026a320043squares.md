---
bibkey: mazhang2026a320043squares
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "OEIS A320043, COMMENTS, revision 43: a square-value refutation extending Zhu's Pell-prime result (2011)"
doi: 10.5281/zenodo.24058057
url: https://zenodo.org/records/24058057
claim: "Corollary 6: for n >= 1 and 1 <= k <= n, with X(n,k) = (n+1-k)^2 k / gcd(n+1-k,k)^3, one has X(2m-1,m) = 1 for m >= 1, prod_{k=1}^{n} X(n,k)^(1/3) = B(n+1) with B(N) = prod_{k=1}^{N} k/gcd(k,N) (A119619), and B(p) = (p-1)! for prime p."
strata_touched:
  - D5/S3/ArithSums/SpeziaA320043RowProduct
license: CC-BY-4.0
triage: anchor
---

# The A320043 row product

## Verified locator

Zenodo record: https://zenodo.org/records/24058057

DOI: 10.5281/zenodo.24058057 (version 2; Zenodo publication date 2026-11-08, PDF dated
November 5, 2026). Source PDF:
https://zenodo.org/api/records/24058057/files/note-v2.pdf/content (text extracted locally,
19,673 characters). Corollary 6 is in Section 3, PDF page 4.

## Source statement

> The triangle entry A322550 states a product formula added by Spezia on June 24, 2024 [2]. It
> follows directly from the same gcd reduction; it is unaffected by the square-value conjecture.

> Corollary 6. For n ≥ 1 and 1 ≤ k ≤ n, put X(n, k) = (n + 1 − k)² k/ gcd(n + 1 − k, k)³. Then
> X(2m − 1, m) = 1 for every m ≥ 1, and ∏_{k=1}^{n} X(n, k)^{1/3} = B(n + 1),
> B(N) = ∏_{k=1}^{N} k/gcd(k, N) (A119619). Moreover B(p) = (p − 1)! for prime p.

> Proof. The central entry has numerator m³ and denominator m³. For the product,
> gcd(n + 1 − k, k) = gcd(n + 1, k) …

## Mathematical scope

X(n, k) is the n-th antidiagonal of Spezia's triangle A322550 (see `spezia2018a320043`), whose
row sums are A320043. B is OEIS A119619 (M. Fuller, 2006); the prime value B(p) = (p − 1)! is
Steinerberger's 2006 comment there. The paper's attribution table marks the product formula as
"Reproved; prior formula Spezia (2024)", so the identity is literature-attested; the note
supplies a proof by the gcd reduction gcd(n + 1 − k, k) = gcd(n + 1, k).
