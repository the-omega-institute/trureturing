---
bibkey: mazhang2026weightedminors
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "Proof of the weighted-minor inequality in MathOverflow 469781 (version 2)"
doi: 10.5281/zenodo.23931738
url: https://zenodo.org/records/23931738
claim: "Theorem 1: for n >= 3, ||z|| = 1 and <z,x> = <z,y> = 0, for arbitrary real symmetric off-diagonal weights a_ij, sum_{i<j} a_ij p_ij^2 <= sum_{i<j<k} max{a_ij, a_ik, a_jk} q_ijk^2, where p_ij = x_i y_j - x_j y_i and q_ijk is the 3x3 determinant with rows x, y, z and columns i, j, k; moreover sum p_ij^2 = sum q_ijk^2. Lemma 2: under the same vector hypotheses every pair family F satisfies sum_{{i,j} in F} p_ij^2 <= sum_{T in N(F)} q_T^2, where N(F) is the set of triples containing a pair of F. Corollary 3: Theorem 1 holds for x, y, z in C^n with Hermitian orthogonality and squared absolute values. Corollary 4: under the hypotheses of Theorem 1 or its complex version, sum min{a_ij, a_ik, a_jk}|q_ijk|^2 <= sum a_ij |p_ij|^2 <= sum max{a_ij, a_ik, a_jk}|q_ijk|^2."
strata_touched:
  - D5/S3/Geometry/ProbabilityTransport/WeightedProjectionMinorsHermitian
license: CC-BY-4.0
triage: anchor
---

# Signed, complex and two-sided weighted-minor comparison

## Verified locator

Zenodo record: https://zenodo.org/records/23931738

DOI: 10.5281/zenodo.23931738 (version 2; concept DOI 10.5281/zenodo.23931737). Source PDF:
https://zenodo.org/api/records/23931738/files/note-v2.pdf/content (text extracted locally with
layout preserved, 17,233 characters). Theorem 1 is in Section 1; Lemma 2 in Section 2; the
proof of Theorem 1 and Corollaries 3 and 4 in Section 3.

## Source statement

> For x, y, z ∈ Rⁿ, put p_ij = x_i y_j − x_j y_i, q_ijk = det(x_i x_j x_k; y_i y_j y_k; z_i z_j z_k).

> Theorem 1. Let n ≥ 3, ‖z‖ = 1, and ⟨z, x⟩ = ⟨z, y⟩ = 0. For arbitrary real symmetric
> off-diagonal weights a_ij, Σ_{i<j} a_ij p_ij² ≤ Σ_{i<j<k} max{a_ij, a_ik, a_jk} q_ijk². (1)

> For u = x ∧ y and b = z ∧ u, the hypotheses of Theorem 1 give ι_z b = u,
> ‖b‖² = ‖u‖² = Σ_{i<j} p_ij² = Σ_{i<j<k} q_ijk². (2)

> For a family F of unordered pairs from [n] = {1, . . . , n}, define
> N(F) = {T ⊆ [n] : |T| = 3 and some S ∈ F satisfies S ⊂ T}.
> Lemma 2. Under the vector hypotheses of Theorem 1, every pair family satisfies
> Σ_{{i,j}∈F, i<j} p_ij² ≤ Σ_{{i,j,k}∈N(F), i<j<k} q_ijk². (3)

> Corollary 3. Theorem 1 holds for x, y, z ∈ Cⁿ, with Hermitian orthogonality and squared
> absolute values of the minors.

> Corollary 4 (Two-sided comparison). Under the hypotheses of Theorem 1, or its complex version,
> Σ_{i<j<k} min{a_ij, a_ik, a_jk}|q_ijk|² ≤ Σ_{i<j} a_ij |p_ij|² ≤ Σ_{i<j<k} max{a_ij, a_ik, a_jk}|q_ijk|².

## Mathematical scope

The formalization works uniformly over 𝕜 = ℝ or ℂ (any `RCLike` field) for `x, y, z` in the
Euclidean space on `Fin n`, with `‖z‖ = 1` and `⟪z, x⟫ = ⟪z, y⟫ = 0`, where the inner product is
conjugate-linear in its first argument, so the contraction is Σ_k conj(z_k) q_kij = p_ij. The
dimension bound n ≥ 3 is dropped: for n ≤ 2 every statement still holds. Formalized are
identity (2) in increasing indices, Lemma 2 for every symmetric pair relation F (the sum over
N(F) restricted to triples having at least one pair in F), and both bounds of Corollary 4 for
arbitrary real symmetric weights, which contain Theorem 1 and Corollary 3. The exterior-algebra
argument is replaced by an equivalent coordinate argument: a Hermitian energy identity for
z ∧ (·), a Cauchy–Schwarz contraction bound, projection locality, a level-set expansion of the
weights, and the constant shift using (2).
