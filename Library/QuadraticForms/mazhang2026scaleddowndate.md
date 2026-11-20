---
bibkey: mazhang2026scaleddowndate
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)"
doi: 10.5281/zenodo.23920598
url: https://zenodo.org/records/23920598
claim: "Theorem 1: for a real symmetric A and x with Delta = x^T A x != 0, w = Ax and M = A - w w^T / Delta, In(M) = (n_+(A) - 1, n_-(A), n_0(A) + 1) if Delta > 0 and (n_+(A), n_-(A) - 1, n_0(A) + 1) if Delta < 0. Corollary 4: under Theorem 1, for M_t = A - t w w^T / Delta, componentwise In(M_t) = In(A) - In([Delta]) + In([(1 - t) Delta]); thus t < 1 preserves inertia, t = 1 gives Theorem 1, and t > 1 replaces one eigenvalue sign by its opposite without changing nullity."
strata_touched:
  - D5/S3/QuadraticForms/StructuredRankOneScaledInertia
license: CC-BY-4.0
triage: anchor
---

# Coefficient-dependent inertia of the structured downdate

## Verified locator

Zenodo record: https://zenodo.org/records/23920598

DOI: 10.5281/zenodo.23920598 (version 2; concept DOI 10.5281/zenodo.23920597). Source PDF:
https://zenodo.org/api/records/23920598/files/note-v2.pdf/content (text extracted locally with
layout preserved, 21,760 characters). Theorem 1 and Corollary 4 are in Section 1.

## Source statement

> Theorem 1. Let A ∈ R^{n×n} be symmetric and x ∈ R^n satisfy ∆ = xᵀAx ≠ 0. Put w = Ax and
> M = A − wwᵀ/∆. Then In(M) = (n₊(A) − 1, n₋(A), n₀(A) + 1) if ∆ > 0, and
> (n₊(A), n₋(A) − 1, n₀(A) + 1) if ∆ < 0. (1)

> Corollary 4 (Coefficient changes). Under Theorem 1, put M_t = A − twwᵀ/∆. Then, componentwise,
> In(M_t) = In(A) − In([∆]) + In([(1 − t)∆]). Thus t < 1 preserves inertia, t = 1 gives (1), and
> t > 1 replaces one eigenvalue sign by its opposite without changing nullity.

## Mathematical scope

Theorem 1 is the frozen StructuredRankOneInertia.inertia_downdate. Corollary 4 is formalized for
every real t, with the componentwise identity stated additively in ℕ:
n₊(M_t) + [∆ > 0] = n₊(A) + [(1 − t)∆ > 0], n₋(M_t) + [∆ < 0] = n₋(A) + [(1 − t)∆ < 0], and
n₀(M_t) = n₀(A) + [t = 1]; the three consequences for t < 1, t = 1 (M_1 equals the structured
downdate) and t > 1 are stated explicitly. The proof uses the congruences of A ⊕ [c] with the
bordered matrix with corner ∆ + c, and of that bordered matrix with corner d with
(A − wwᵀ/d) ⊕ [d], for d = ∆/t and c = d − ∆, together with Sylvester's law of inertia.
