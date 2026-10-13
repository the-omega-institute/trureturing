---
bibkey: hiai2025geometrictraceconvexity
authors: Fumio Hiai
year: 2026
title: Log-majorizations between quasi-geometric type means for matrices
doi: 10.1016/j.laa.2026.01.003
url: https://arxiv.org/abs/2510.04691v3
claim: Equations (2.1)/(2.2) identify the original geometric trace; Problem 5.18 asks its joint convexity on the interior parameter rectangle.
strata_touched:
  - D5/S3/Quantum/Hiai
license: citation-only
triage: anchor
---

# Original geometric trace and support extension

This entry carries the canonical DOI metadata for the article and records
its Problem 5.18 application. The companion note
[`hiai2025logmajorizationle`](hiai2025logmajorizationle.md) records
Problem 3.20 and links back to this publication entry.

The author-deposited v3 is explicitly labelled “Final print version” in the
arXiv metadata, updated 20 January 2026, and associated with the published
article in Linear Algebra and its Applications 735 (2026), 123–174.
Problem 5.18 remains explicitly open in that author-final text. This
identifies the author-deposited publication version; the publisher body
was not independently compared.

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

For alpha>1 the original domain consists of PSD pairs with
s(B)<=s(A), equivalently ker A contained in ker B (Section 2, page 5).
Proposition 2.1(2), page 5, gives the simultaneous additive epsilon-I
limit; Proposition 5.16(4), pages 31–32, uses it to reduce PSD to PD.
These assertions concern G, the classical base-first mean, rather
than SG or tilde-SG.

The PSD extension in GeometricTraceConvexity proves that limit for the
actual CFC formula. With Q=I-spectralSupport(A), both A Q and B Q
vanish. Finite spectral calculus splits (A+epsilon I)^(-p/2) into
a support-restricted factor and epsilon^(-p/2) Q. The exact powered
B regularization acts on Q as epsilon^p Q, so the inner sandwich
splits as the supported sandwich plus Q. Its support-restricted
negative factors converge on the fixed finite spectrum; positive
powers and trace are continuous on PSD. Spectral intertwining and
the outer A^(p/2) factors remove Q at the limit, identifying the
unchanged Moore–Penrose formula. The paired domain is convex by
PSD quadratic forms. Apply the SPD inequality to the common epsilon-I
regularizations and pass the three trace limits through closed order.

The resulting ConvexOn endpoint includes singular supported pairs,
empty carriers and both closed parameter intervals. It uses neither
arbitrary continuity on the paired domain nor the SPD reverse-base
identity at singular B. The literature fixes the target and supplies
the ordinary boundary argument; it does not replace the Lean proof
or establish a global novelty claim.

## Verified locator

Published article DOI: https://doi.org/10.1016/j.laa.2026.01.003.
Source page: https://arxiv.org/abs/2510.04691v3.
Primary PDF: https://arxiv.org/pdf/2510.04691v3.
SHA256: 517793e372e0d145619e517e7be0772e4852536ce65821cd5142e714e19e1a4b.
The cached extracted text has SHA256
aa28e51ce917d745be733f307d25bd1322fe0fa2f34b0db0032eb69a9ecbf8a5.
Its byte-LF lines 122-124 state support semantics, 139-142 contain
(2.1)/(2.2), and 2045-2047 state Problem 5.18. No proof text is
transcribed from the paper; it fixes the target and applicability boundary.

The bounded later-primary check inspected arXiv:2609.00034v1
(alternative means and data processing), arXiv:2512.22807v1
(spectral-family Ando–Hiai inequalities), and arXiv:2609.32095v1
(local determinant defects for the alpha–z Renyi kernel, equation (47)
and comparison section 8.4). None of those inspected results supplies
original-G joint convexity. This bounded search does not establish
worldwide priority of the repository solution.
