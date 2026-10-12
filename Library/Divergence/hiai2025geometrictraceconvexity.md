---
bibkey: hiai2025geometrictraceconvexity
authors: Fumio Hiai
year: 2025
title: Log-majorizations between quasi-geometric type means for matrices
doi: null
url: https://arxiv.org/abs/2510.04691v3
claim: Equations (2.1)/(2.2) identify the original geometric trace; Problem 5.18 asks its joint convexity on the interior parameter rectangle.
strata_touched:
  - D5/S3/Quantum/Hiai
license: citation-only
triage: anchor
---

# Original geometric trace and SPD variational assembly

On page 4, (2.1) defines the base-first mean
A #alpha B = A^(1/2) (A^(-1/2) B A^(-1/2))^alpha A^(1/2).
Equation (2.2) defines G(alpha,p)(A,B)=(A^p #alpha B^p)^(1/p).
Problem 5.18, page 33, asks whether Tr G(alpha,p) is jointly convex
for 1<alpha<2 and 1/2<=p<1. These are the original geometric
functional and order of arguments, not the spectral geometric mean.
The support/generalized-inverse convention is stated on page 3:
negative powers invert only on the support and vanish on the kernel.

The connected Lean assembly proves joint convexity of Re Tr G(alpha,p)
on SPD x SPD for alpha in [1,2] and p in [1/2,1], in every finite complex
matrix dimension including empty. All powers use spectral CFC.
It consumes the existing all-real geometric identification, the attained
inverse trace variational bound, Carlen-Lieb fixed-congruence convexity,
and Hiai mean-trace Psi concavity. Those classical suppliers are credited
in the existing library notes `hiai2025geometricidentification`,
`carlenlieb2008minkowski`, `hiai2015meanconcavity`, and
`zhang2020variational`; the compatible Physlib ports retain Apache-2.0
attribution and their pinned revision. No reused theorem is claimed novel.

Put theta=alpha-1, X=B^p and M=B^p #theta A^p. Weighted symmetry
and inverse sandwich give A^p #alpha B^p=X inverse(M) X.
The inverse variational objective at r=1/p becomes
2 Re Tr((Z adjoint B^(2p) Z)^(1/(2p)))
minus Re Tr((Z adjoint M Z)^(1/p)). For each fixed invertible Z,
the first term is convex at the Carlen-Lieb exponent a=2p in [1,2],
and the second term is concave by the existing Psi theorem.
Choose the attained invertible optimizer at the mixed point only.
Its objective equals the mixed target. Fixed-optimizer convexity and
the two universal endpoint variational bounds give the desired estimate.
The optimizer need not be selfadjoint; no optimizer uniqueness,
compactness, or abstract supremum attainment is needed.

This settles the SPD intermediate, not the full original PSD domain.
The unpaid obligations are support inclusion s(A)>=s(B), generalized
inverse zero on kernels, the same epsilon I on original A and B before
p-powers, a norm/trace limit, and convexity of that support domain.
No compression or block-support transport is assumed proved.

## Source binding

Primary PDF: https://arxiv.org/pdf/2510.04691v3.
SHA256: 517793e372e0d145619e517e7be0772e4852536ce65821cd5142e714e19e1a4b.
The cached extracted text has SHA256
aa28e51ce917d745be733f307d25bd1322fe0fa2f34b0db0032eb69a9ecbf8a5.
Its byte-LF lines 122-124 state support semantics, 139-142 contain
(2.1)/(2.2), and 2045-2047 state Problem 5.18. No proof text is
transcribed from the paper; it fixes the target and applicability boundary.
