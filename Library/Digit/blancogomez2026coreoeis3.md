---
bibkey: blancogomez2026coreoeis3
authors: Roberto Blanco Gómez
year: 2026
title: "Open statements in core entries of the OEIS, III: Benford's law for the Bell numbers, Bala's congruences for the Motzkin numbers, and further proofs"
doi: 10.5281/zenodo.23150301
url: "https://zenodo.org/records/23150301"
claim: "Proposition 9.1 (A000290): for n >= 1, the least k such that there are A, B ⊆ {0, ..., n^2 - 1} with |A| = |B| = k and A + B ⊇ {0, ..., n^2 - 1} is n. This is M. Chu's conjecture (2022)."
strata_touched:
  - D5/S3/Arith/Additive/ChuSquareCovering
license: citation-only
triage: anchor
---

# Additive covers of an initial interval

## Verified locator

Zenodo record 10.5281/zenodo.23150301, English PDF `Blanco_Gomez_2026_core_OEIS_III_EN.pdf`,
Section 9, Proposition 9.1, page 8.

## Source statement

> Proposition 9.1 (A000290). For n ≥ 1, the least k such that there are A, B ⊆ {0, …, n² − 1}
> with |A| = |B| = k and A + B ⊇ {0, …, n² − 1} is n.

The source's proof: |A + B| ≤ |A||B| = k², so k ≥ n; conversely A = {0, …, n − 1} and
B = {0, n, 2n, …, (n − 1)n} lie in {0, …, n² − 1} and A + B = {0, …, n² − 1} by division by n.

## Mathematical scope

ChuSquareCovering.result states Proposition 9.1 for every n, n = 0 included (then k = 0 with
A = B = ∅). ChuSquareCovering.achievable_iff determines every pair of sizes for an arbitrary
interval {0, …, N − 1}: sets A, B in it with |A| = a, |B| = b and A + B ⊇ {0, …, N − 1} exist
exactly when N ≤ ab, a ≤ N and b ≤ N. For sufficiency B consists of the multiples of a below N,
completed to b elements inside the interval.
