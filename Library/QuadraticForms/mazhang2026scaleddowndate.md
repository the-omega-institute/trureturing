---
bibkey: mazhang2026scaleddowndate
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: "MathOverflow 513954, revision 2: singular signed downdates, fixed coordinates, and a sharp polynomial sphere bound (version 2)"
doi: 10.5281/zenodo.23920598
url: https://zenodo.org/records/23920598
claim: "Theorem 1: for a real symmetric A and x with Delta = x^T A x != 0, w = Ax and M = A - w w^T / Delta, In(M) = (n_+(A) - 1, n_-(A), n_0(A) + 1) if Delta > 0 and (n_+(A), n_-(A) - 1, n_0(A) + 1) if Delta < 0. Corollary 3: for a real symmetric A, X in R^(n x k) and invertible G = X^T A X, N = A - A X G^(-1) X^T A has In(N) = (n_+(A) - n_+(G), n_-(A) - n_-(G), n_0(A) + k), ker N = ker A (+) im X and rank N = rank A - k. Corollary 4: under Theorem 1, for M_t = A - t w w^T / Delta, componentwise In(M_t) = In(A) - In([Delta]) + In([(1 - t) Delta]); thus t < 1 preserves inertia, t = 1 gives Theorem 1, and t > 1 replaces one eigenvalue sign by its opposite without changing nullity. Theorem 5: for a nonempty connected topological space Y and continuous d, x : Y -> R^n with D = diag(d_i), Delta = x^T D x and M = D - D x x^T D / Delta, if Delta != 0 and M is positive semidefinite everywhere, then either Delta > 0 everywhere and all d_i >= 0, or Delta < 0 everywhere and a unique index j satisfies d_j < 0 everywhere while all other d_i >= 0 everywhere. Corollary 7: the finite-puncture simplex conclusion of Corollary 6 remains true when the deleted set is countable. Corollary 8: the threshold n >= 3 in Corollary 6 is sharp for a conclusion uniform over all finite deleted sets. Corollary 10: with active coordinates, h = 1 has fixed-dimension infimum 1/sqrt d and all-dimension infimum 0, while at most two coordinates give infimum 1/sqrt 2; for h(t) = 1/t the infimum is 0 already in dimension two. Theorem 11: for h(t) = (3t - t^3)/2 on [0, 1], h is strictly increasing, h(1) = 1 and h(t)/t = (3 - t^2)/2 is strictly decreasing for 0 < t <= 1; over nonnegative unit vectors of arbitrary finite dimension, inf R_h(x)^2 = 16(17 - 9 sqrt 3)/23, not attained in finite dimension; at most two nonzero coordinates give the attained minimum 80/81; squared coordinates (4/5, 1/10, 1/10) give 13689/13885 < 80/81; the infimum is approached by one squared coordinate a* = 6 - 3 sqrt 3 and m squared coordinates (1 - a*)/m."
strata_touched:
  - D5/S3/QuadraticForms/StructuredRankOneScaledInertia
  - D5/S3/QuadraticForms/StructuredRankOneFamily
  - D5/S3/QuadraticForms/StructuredRankOneBlockRemoval
  - D5/S3/QuadraticForms/CubicSphereInfimum
  - D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation
  - D5/S3/QuadraticForms/SphereRatioEarlierExamples
license: CC-BY-4.0
triage: anchor
---

# Coefficient-dependent inertia and continuous families of structured downdates

## Verified locator

Zenodo record: https://zenodo.org/records/23920598

DOI: 10.5281/zenodo.23920598 (version 2; concept DOI 10.5281/zenodo.23920597). Source PDF:
https://zenodo.org/api/records/23920598/files/note-v2.pdf/content (text extracted locally with
layout preserved, 21,760 characters). Theorem 1 and Corollaries 3 and 4 are in Section 1; Theorem 5 and Corollary 7 in Section 2.

## Source statement

> Theorem 1. Let A ∈ R^{n×n} be symmetric and x ∈ R^n satisfy ∆ = xᵀAx ≠ 0. Put w = Ax and
> M = A − wwᵀ/∆. Then In(M) = (n₊(A) − 1, n₋(A), n₀(A) + 1) if ∆ > 0, and
> (n₊(A), n₋(A) − 1, n₀(A) + 1) if ∆ < 0. (1)

> Corollary 3 (Nondegenerate block removal). Let A be real symmetric, X ∈ R^{n×k}, and G = XᵀAX
> invertible. Define N = A − AXG⁻¹XᵀA. Then In(N) = (n₊(A) − n₊(G), n₋(A) − n₋(G), n₀(A) + k),
> ker N = ker A ⊕ im X, rank N = rank A − k.

> Corollary 4 (Coefficient changes). Under Theorem 1, put M_t = A − twwᵀ/∆. Then, componentwise,
> In(M_t) = In(A) − In([∆]) + In([(1 − t)∆]). Thus t < 1 preserves inertia, t = 1 gives (1), and
> t > 1 replaces one eigenvalue sign by its opposite without changing nullity.

> Theorem 5. Let Y be a nonempty connected topological space, and let d, x : Y → Rⁿ be continuous.
> For y ∈ Y define D(y) = diag(d₁(y), . . . , dₙ(y)), ∆(y) = x(y)ᵀD(y)x(y),
> M(y) = D(y) − D(y)x(y)x(y)ᵀD(y)/∆(y). Suppose ∆(y) ≠ 0 and M(y) ⪰ 0 for every y. Then exactly one of
> the following alternatives holds: 1. ∆(y) > 0 and every dᵢ(y) ≥ 0 for all y; 2. ∆(y) < 0 for all y,
> and there is a unique index j such that dⱼ(y) < 0 for every y and dᵢ(y) ≥ 0 for every i ≠ j and
> every y.

> Corollary 6. Let n ≥ 3, let X be homeomorphic to an open (n − 1)-simplex, and let F ⊂ X be finite.
> With Y = X \ F, all conclusions of Theorem 5 hold under its stated continuity, nonzero-pivot and
> positive-semidefiniteness hypotheses.

> Corollary 7 (Countably many punctures). Corollary 6 remains true for countable F.

> Corollary 8 (Sharp dimension threshold). The dimension threshold n ≥ 3 in Corollary 6 is
> sharp for a conclusion uniform over all finite deleted sets.
>
> Proof. For n = 2, let X = (−1, 1) and F = {0}. On y < 0 take D = diag(−1, 1) and
> x = (1, 0)ᵀ; on y > 0 take D = diag(1, −1) and x = (0, 1)ᵀ. These functions are continuous
> on X \ F, with ∆ = −1 and M ⪰ 0 everywhere, but the index of the negative diagonal entry
> switches between the two components.

> Corollary 10 (Infima for the earlier examples). Under the active-coordinate convention, h = 1
> has fixed-dimension infimum 1/√d, and all-dimension infimum zero, whereas dimensions at most two
> give infimum 1/√2. For h(t) = 1/t, the infimum is already zero in dimension two.

> Theorem 11 (An increasing odd polynomial). Let h(t) = (3t − t³)/2 on [0, 1]. It is strictly
> increasing, h(1) = 1, and h(t)/t = (3 − t²)/2 is strictly decreasing for 0 < t ≤ 1. Over
> nonnegative unit vectors of arbitrary finite dimension,
> inf R_h(x)² = 16(17 − 9√3)/23. (4)
> The infimum is not attained in a finite dimension. Restricting to at most two nonzero
> coordinates gives the attained minimum 80/81 instead. For example, a vector with squared
> coordinates (4/5, 1/10, 1/10) gives R_h(x)² = 13689/13885 < 80/81. The infimum in (4) is
> approached by one squared coordinate a* = 6 − 3√3 and m squared coordinates (1 − a*)/m as
> m → ∞.

## Mathematical scope

Theorem 1 is the frozen StructuredRankOneInertia.inertia_downdate. Corollary 4 is formalized for
every real t, with the componentwise identity stated additively in ℕ:
n₊(M_t) + [∆ > 0] = n₊(A) + [(1 − t)∆ > 0], n₋(M_t) + [∆ < 0] = n₋(A) + [(1 − t)∆ < 0], and
n₀(M_t) = n₀(A) + [t = 1]; the three consequences for t < 1, t = 1 (M_1 equals the structured
downdate) and t > 1 are stated explicitly. The proof uses the congruences of A ⊕ [c] with the
bordered matrix with corner ∆ + c, and of that bordered matrix with corner d with
(A − wwᵀ/d) ⊕ [d], for d = ∆/t and c = d − ∆, together with Sylvester's law of inertia.

Theorem 5 is formalized as StructuredRankOneFamily.connected_family for any topological space Y
with `ConnectedSpace Y` (which includes nonemptiness) and continuous d, x : Y → (Fin n → ℝ); the
downdate is diag(d) − ∆⁻¹ (Dx)(Dx)ᵀ, the paper's M. "Exactly one" is written as a disjunction; the
alternatives exclude each other because Y is nonempty and the sign of ∆ at one point decides. Corollary 7
is StructuredRankOneFamily.countable_family: for n ≥ 3 and any X with a homeomorphism onto the model
open simplex {u ∈ ℝⁿ⁻¹ : uᵢ > 0, Σuᵢ < 1}, and any countable A ⊆ X, the complement is nonempty and the
conclusion of Theorem 5 holds on it. Path connectedness of the complement is proved by transporting A
through the log-ratio chart to ℝⁿ⁻¹ and applying Mathlib's countable-complement theorem, in place of
the paper's small-circle argument. The existing finite-puncture theorem (Corollary 6) is derived from
these.

Corollary 3 is formalized as StructuredRankOneBlockRemoval.result for X : Matrix ι κ ℝ (k = |κ|) with
det G a unit: N and G are symmetric, n₊(A) = n₊(N) + n₊(G) and n₋(A) = n₋(N) + n₋(G) (the
subtractions stated additively), n₀(N) = n₀(A) + k, ker N = ker A ⊔ im X with ker A and im X
disjoint and X injective, and rank N + k = rank A. The kernel, injectivity, nullity and rank
statements (StructuredRankOneBlockRemoval.kernel_split) hold for any square matrix over any field,
without symmetry. The proof uses the congruences of A ⊕ 0 with the
matrix bordered by AX and corner G, and of that matrix with N ⊕ G, rather than an adapted basis.

Corollary 8 is StructuredRankOneDimensionTwoRefutation.result, the negation of
StructuredRankOneDimensionTwoRefutation.claim: for some point c of the model open 1-simplex
(0, 1), continuous data on (0, 1) \ {c} with nonzero pivot and positive semidefinite downdate have
pivot positive everywhere or a fixed diagonal entry negative everywhere. Both alternatives of
Corollary 6 imply this weak form. The refutation uses the source's data on the two components of
(0, 1) \ {c} for every c, so the conclusion fails after deleting any one point.

Corollary 10 is SphereRatioEarlierExamples.result, over unit vectors with all d coordinates
positive. For h = 1 it gives the infimum 1/√d in each dimension d ≥ 1 (unattained for d ≥ 2), the
all-dimension infimum 0 and the infimum 1/√2 over dimensions at most two, all unattained. For
h(t) = 1/t it gives the infimum 0, unattained, in every dimension d ≥ 2, which is stronger than
the source's dimension two. The example h = 1 is due to daw (comment 11110291) and h(t) = 1/t to
Exodd (answer 5146715) on Mathematics Stack Exchange 5146381.

Theorem 11 answers Lucid's sphere question, Mathematics Stack Exchange 5146381, linked from
MathOverflow 513954, revision 2. It is formalized as CubicSphereInfimum.result, with R_h(x) = Σᵢ xᵢ h(xᵢ) / (Σᵢ h(xᵢ)²)^{1/2}
(h(0) = 0, so summing over all coordinates agrees with the active-coordinate convention). Three
statements are stronger than the source: h is strictly increasing on [−1, 1]; h(t)/t is strictly
decreasing for every t > 0; and the strict bound 16(17 − 9√3)/23 < R_h(x)² and the two-coordinate
bound 80/81 ≤ R_h(x)² hold for unit vectors of any signs, since both depend only on the squared
coordinates pᵢ = xᵢ². The moment identity R_h(x)² = (3 − s₂)²/(9 − 6s₂ + s₃), sₖ = Σ pᵢᵏ, is
CubicSphereInfimum.moment. The lower bound uses s₃ ≤ a s₂ = a³ for a = √s₂ and the factorization
23(3 − a²)² − 16(17 − 9√3)(9 − 6a² + a³) = (a − a*)²(23a² + (4 + 6√3)a + 12√3 − 15), whose second
factor is positive for a ≥ 0, in place of the paper's sign analysis of f′; equality would force
every positive pᵢ to equal a, hence a = 1 ≠ a*. On supports of at most two points 2s₃ = 3s₂ − 1
and R_h(x)² − 80/81 = (9s₂ − 7)²/(81(9 − 6s₂ + s₃)), so equality holds exactly when 9s₂ = 7,
for instance for squared coordinates (3 ± √5)/6.
