---
bibkey: mazhang2026hermitesignedmode
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Resolving the Hermite coefficient conjectures in OEIS A381423, Comments (revision 8)"
doi: 10.5281/zenodo.23957586
url: https://zenodo.org/records/23957586
claim: "Theorem 1: for every n >= 0, the largest signed coefficient of the physicists' Hermite polynomial H_n is unique, and q(n) = floor((2n + 7 - sqrt(8n + 21))/8), a(n) = n - 4q(n); equivalently a(n) is the least nonnegative integer j congruent to n mod 4 with j^2 + 7j + 7 >= 2n; moreover a(n+1) - a(n) is 1 or -3."
strata_touched:
  - D5/S3/Analytic/Polynomial/HermiteSignedModeThreshold
license: CC-BY-4.0
triage: anchor
---

# Unique signed Hermite mode and its quadratic threshold

## Verified locator

Zenodo record: https://zenodo.org/records/23957586

DOI: 10.5281/zenodo.23957586 (version 3; Zenodo publication date 2026-11-04, PDF dated
3 November 2026; concept DOI 10.5281/zenodo.23957585). Source PDF:
https://zenodo.org/api/records/23957586/files/note-v3.pdf/content (text extracted locally with
layout preserved, 20,124 characters). Theorem 1 is in Section 1.

## Source statement

> Write a(n) for the least j ∈ {0, . . . , n} at which [x^j]H_n(x) is maximal, comparing signed
> coefficients.

> Theorem 1. For every n ≥ 0, the largest signed coefficient of H_n is unique, and
> q(n) = ⌊(2n + 7 − √(8n + 21))/8⌋, a(n) = n − 4q(n). (2)
> Equivalently, a(n) is the least nonnegative integer j ≡ n (mod 4) such that
> F(j) := j² + 7j + 7 ≥ 2n. (3)
> Moreover, a(n + 1) − a(n) ∈ {1, −3} for every n ≥ 0.

## Mathematical scope

H_n uses the physicists' normalization of DLMF 18.5.13, as in the frozen HermiteSignedMode
module, whose result already gives the least maximizer a(n) and the differences 1 and −3. The
remaining clauses are formalized: every other exponent, including those above n, has a strictly
smaller coefficient; among j ≡ n (mod 4), a(n) ≤ j exactly when F(j) ≥ 2n, so a(n) is the least
such j; and a(n) = n − 4q(n) with the
radical floor formula over the reals. The source credits Mike Sheppard (OEIS A381423, revision 8)
for the questions and DLMF 18.5.13 for the coefficient formula.
