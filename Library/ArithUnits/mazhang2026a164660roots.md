---
bibkey: mazhang2026a164660roots
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "OEIS A164660, final FORMULA (29 May 2016): Chebyshev numerators and floor products"
doi: "10.5281/zenodo.23884883"
url: "https://doi.org/10.5281/zenodo.23884883"
claim: "Proposition 3: for positive n, r, the r-th power roots of 0 modulo n in any n consecutive integers number C_r(n) = n/D_r(n), the translated floor product is (-1)^{C_r(n)}, C_r(n) = n/rad(n) iff r is at least every exponent of n, and for r >= 2 the product equals A164660(n+1)."
strata_touched:
  - D5/S3/ArithSums/BrowneA164660RootCount
license: citation-only
triage: anchor
---
<!-- GID: D5/L/ArithUnits/mazhang2026a164660roots -->
# Arbitrary-power root counts for Browne's floor product

## Verified locator

The written proof is by **Haobo Ma and Wenlin Zhang**, *OEIS A164660, final FORMULA
(29 May 2016): Chebyshev numerators and floor products*, version 1, exact-version DOI
https://doi.org/10.5281/zenodo.23884883 (concept DOI 10.5281/zenodo.23884882), Proposition 3.
The sequence is W. Lang's OEIS A164660 (2009); the final FORMULA is A. Browne's (29 May 2016).
The square, cube and fourth-power root counts are OEIS A000188, A000189 and A000190;
S. Finch, arXiv:math/0605019v2, Section 2, discusses nilpotent residues.

## Statement

For positive integers n and r write n as the product of p^(e_p), put
D_r(n) = product of p^(ceil(e_p/r)) and C_r(n) = n/D_r(n). For every integer k, n divides k^r
if and only if D_r(n) divides k. Hence each window s+1, ..., s+n of consecutive integers
contains exactly C_r(n) solutions, the floor differences floor(k^r/n) - floor((k^r-1)/n) sum
to C_r(n), and the product of 1 - 2 times them is (-1)^(C_r(n)). For n > 1, C_r(n) = n/rad(n)
exactly when r is at least every exponent e_p. For r >= 2, C_r(n) is even exactly when 4
divides n, so the product equals A164660(n+1).
