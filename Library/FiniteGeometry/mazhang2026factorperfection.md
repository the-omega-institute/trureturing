---
bibkey: mazhang2026factorperfection
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Resolving Pozsgay–Wanless's factor-perfection question and qubit decomposition conjecture"
doi: 10.5281/zenodo.23903313
url: https://zenodo.org/records/23903313
claim: "Lemma 2: if square matrices M1, ..., Mm of the same size have nonnegative integer entries and Mm ... M1 is a permutation matrix, then every Mj is a permutation matrix."
strata_touched:
  - D5/S3/Combinatorics/Latin/NonnegativePermutationFactors
license: CC-BY-4.0
triage: anchor
---

# Nonnegative integer factors of a permutation matrix

## Verified locator

DOI: 10.5281/zenodo.23903313 (version 2; PDF dated 2 November 2026). Source PDF:
https://zenodo.org/api/records/23903313/files/note-v2.pdf/content (text extracted locally,
about 26,400 characters). Lemma 2 is in Section 2, before the definition of the binary
tensors in equation (3).

## Source statement

> Lemma 2. If square matrices M1, . . . , Mm of the same size have nonnegative integer
> entries and Mm · · · M1 is a permutation matrix, then every Mj is a permutation matrix.

> Thus every row sum of Mm is one. Each row consists of a single one and zeros, and
> nonsingularity makes those ones occupy distinct columns. Consequently Mm is a permutation
> matrix. Multiply by Mm−1 and repeat for the remaining product.

## Mathematical scope

The paper applies the lemma to the lifted local flattenings of the classical three-gate
circuit of Pozsgay and Wanless (see `pozsgaywanless2024tensor`), where it turns permutation
flattenings of the composite tensor into permutation flattenings of every factor. The source
proof uses row sums and the all-ones vector. The underlying fact that a nonnegative matrix
with a nonnegative inverse is monomial is classical in nonnegative matrix theory; over the
nonnegative integers the monomial matrix is a permutation matrix.
