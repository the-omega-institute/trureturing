---
bibkey: seowadayamazaki2026andohiai
authors: Yuki Seo; Shuhei Wada; Takeaki Yamazaki
year: 2026
title: On the Ando-Hiai property for spectral geometric means
doi: 10.1016/j.laa.2026.05.013
url: https://arxiv.org/abs/2512.22807
claim: Problem 3.11 asks whether the spectral geometric mean preserves the Ando-Hiai implication for every power between zero and one; Theorem 3.9 proves the implication in a central parameter region.
strata_touched:
  - D5/S3/Quantum/Matrix/SeoWadaYamazakiAndoHiaiRefutation
license: citation-only
triage: anchor
---

# Spectral geometric mean and the Ando-Hiai implication

## Verified locator

Source: https://arxiv.org/abs/2512.22807.
DOI: 10.1016/j.laa.2026.05.013.
The source is arXiv:2512.22807v1, published in Linear Algebra and
its Applications 746 (2026), pages 18-47.

## Definitions and question

For strictly positive operators, the source uses

$$
A\# B=A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2},
\qquad
A\natural_tB=(A^{-1}\#B)^tA(A^{-1}\#B)^t.
$$

The order is the Loewner order. All powers are spectral real powers.
Problem 3.11 asks:

> Let A, B be strictly positive operators and t be in (0,1) other than 1/2.
> Does A natural_t B <= I imply A^q natural_t B^q <= I for all 0 < q <= 1?

This is a transcription of Problem 3.11, with the
spectral geometric mean written in plain text inside the quotation.
The finite dimensional restriction includes positive definite complex two
by two matrices and is sufficient for a refutation.

## Theorem 3.9 and Remark 3.10

Theorem 3.9 supplies the implication when

$$
0<q\le\min\left\{\frac{t}{1-t},\frac{1-t}{t}\right\}.
$$

Equivalently, for fixed $q\in(0,1]$, its sufficient range is

$$
\frac{q}{1+q}\le t\le\frac{1}{1+q}.
$$

Remark 3.10 discusses the remaining parameter range and the numerical search
that motivates Problem 3.11.
The source sufficient direction is not a Lean conclusion of the refutation
module. Later-literature completeness and worldwide priority are not claimed.
