---
bibkey: mazhang2026factorperfection
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Resolving Pozsgay–Wanless's factor-perfection question and qubit decomposition conjecture"
doi: 10.5281/zenodo.23903313
url: https://zenodo.org/records/23903313
claim: "Lemma 2: if square matrices M1, ..., Mm of the same size have nonnegative integer entries and Mm ... M1 is a permutation matrix, then every Mj is a permutation matrix. Lemma 4: if complex n x n matrices M1, ..., Mm have squared Frobenius norm n and Mm ... M1 is unitary, every Mj is unitary."
strata_touched:
  - D5/S3/Combinatorics/Latin/NonnegativePermutationFactors
  - D5/S3/Combinatorics/Latin/NormDeterminantRigidity
license: CC-BY-4.0
triage: anchor
---

# Nonnegative integer and Frobenius-normalized factors

## Verified locator

Zenodo record: https://zenodo.org/records/23903313

DOI: 10.5281/zenodo.23903313 (version 2; PDF dated 2 November 2026). Source PDF:
https://zenodo.org/api/records/23903313/files/note-v2.pdf/content (text extracted locally,
about 25,860 characters). Lemma 2 is in Section 2, before the definition of the binary
tensors in equation (3); Lemma 4 is the first numbered result of Section 3 (p. 4).

## Source statement

> Lemma 2. If square matrices M1, . . . , Mm of the same size have nonnegative integer
> entries and Mm · · · M1 is a permutation matrix, then every Mj is a permutation matrix.

> Thus every row sum of Mm is one. Each row consists of a single one and zeros, and
> nonsingularity makes those ones occupy distinct columns. Consequently Mm is a permutation
> matrix. Multiply by Mm−1 and repeat for the remaining product.

> Lemma 4. Let M1, . . . , Mm be complex n × n matrices with ∥Mj∥²_F = n. If Mm · · · M1 is
> unitary, every Mj is unitary.

> The product of these determinant moduli is one, so equality holds for every factor.
> Equality in the arithmetic–geometric mean inequality forces all its squared singular values
> to be one.

## Mathematical scope

The paper applies the lemma to the lifted local flattenings of the classical three-gate
circuit of Pozsgay and Wanless (see `pozsgaywanless2024tensor`), where it turns permutation
flattenings of the composite tensor into permutation flattenings of every factor. The source
proof uses row sums and the all-ones vector. The underlying fact that a nonnegative matrix
with a nonnegative inverse is monomial is classical in nonnegative matrix theory; over the
nonnegative integers the monomial matrix is a permutation matrix.

Lemma 4 is the quantum counterpart, used for the unitary-gate criterion (Theorem 5) and the
perfect replacement tensors (Theorem 6). Its proof bounds |det Mj|² by the arithmetic–geometric
mean of the squared singular values; the formalization uses the eigenvalues of Mjᴴ Mj and the
inequality x ≤ exp(x − 1), which has the same equality case.
