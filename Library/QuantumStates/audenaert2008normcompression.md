---
bibkey: audenaert2008normcompression
authors: K. M. R. Audenaert
year: 2008
title: "On a norm compression inequality for 2×N partitioned block matrices"
doi: 10.1016/j.laa.2007.08.007
url: https://arxiv.org/abs/math/0702186v2
claim: "Conjecture 1, upper branch: Schatten norm compression for arbitrary 2×N compatible block matrices at p ≥ 2."
strata_touched:
  - D5/S3/Quantum/NormCompression/UpperBranchReduction
license: citation-only
triage: anchor
---

# Norm compression for two block rows

## Verified locator

DOI: 10.1016/j.laa.2007.08.007

Source: https://arxiv.org/abs/math/0702186v2

Linear Algebra and its Applications 428 (2008), 781–795. The arXiv preprint's
page 2 contains the Schatten norm, the compression matrix and Conjecture 1;
Section 4 is entitled "Proofs in Special Cases". The publisher's
DOI metadata matches the author, title, volume and pages.

On page 1, the source defines compression in words:

> The norm compression of a block-partitioned matrix T = [T₍ᵢⱼ₎] w.r.t. a given matrix norm ||.|| is a matrix obtained from T by replacing each of its blocks by their norm: [||T₍ᵢⱼ₎||].

On page 2, the Schatten norm is

$$\|A\|_p=(\operatorname{Tr}(|A|^p))^{1/p}.$$

The compression definition, on the same page, is introduced by:

> I denote by 𝒞ₚ(T) its Schatten p-norm compression,

$$\mathcal C_p(T)=\begin{pmatrix}\|A_1\|_p&\cdots&\|A_N\|_p\\
\|B_1\|_p&\cdots&\|B_N\|_p\end{pmatrix}.$$

Conjecture 1, page 2, verbatim:

> Let T be a general matrix partitioned in 2 × N blocks, and let 𝒞ₚ(T) be its norm compression using the Schatten p-norm, then the following norm compression inequalities hold:

$$\|T\|_p\ge\|\mathcal C_p(T)\|_p,\quad 1\le p\le2,$$
$$\|T\|_p\le\|\mathcal C_p(T)\|_p,\quad p\ge2.$$

The Lean encoding uses `Matrix.toEuclideanLin` and
`LinearMap.singularValues`: the trace power is the finite sum of the p-th
powers of singular values, and the Schatten norm is its real 1/p-th power.
The scalar compression entries are nonnegative real block norms cast to ℂ.
The two row spaces are arbitrary finite types; the finite column dimension
may depend on the column index.

The upper-branch three-column reduction preserves the compression Gram
matrix and increases the original Schatten norm after nonnegative
square-root rescaling. This is a reduction of the upper branch, not a proof
of Conjecture 1. AUD-UP on 2 < p < 4 remains open. The lower-branch reduction
requires trace-power concavity and is not established by this module.
