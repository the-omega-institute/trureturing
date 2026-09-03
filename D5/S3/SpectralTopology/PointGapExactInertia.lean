/- GID: D5/S3/SpectralTopology/PointGapExactInertia
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/PointGapExactInertia
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite point gap gives exact half-dimensional chiral inertia. -/

import D5.S3.SpectralTopology.FiniteSpectralLocalizer
import Mathlib.Data.Fintype.Sum
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Exact inertia of the zero-scale point-gap localizer

The finite spectral-localizer owner already proves that chiral conjugation
balances the positive and negative inertia counts of the zero-scale
Hermitianization and that a finite point gap is equivalent to invertibility of
that Hermitianization.

This node closes the finite-dimensional counting chain. For every Hermitian
matrix, the positive and negative indices partition its nonzero spectrum and
therefore add to its rank. Under a point gap, the zero-scale localizer has full
rank on the doubled carrier. Combining full rank with chiral balance gives

`n₊(L₀) = n₋(L₀) = Fintype.card n`.

Thus the zero-scale signature vanishes for a stronger reason under a point
gap: there are no zero modes, and the doubled finite spectrum splits exactly
into equally many positive and negative eigenvalues.

This remains a finite algebraic statement. It does not establish local
constancy for nonzero position scale, a normalized topological index,
bulk-boundary correspondence, an infinite-volume limit, or RH.
-/

/- Library-search audit trail (2026-09-02):
   * `FiniteSpectralLocalizer` owns zero-scale Hermitianity, chiral inertia
     balance, signature vanishing, and the equivalence between a point gap and
     zero-scale localizer invertibility.
   * `RHLinalg.posIndex` and `RHLinalg.negIndex` own the positive and negative
     eigenvalue counts. Mathlib's
     `Matrix.IsHermitian.rank_eq_card_non_zero_eigs` owns the rank count of
     nonzero Hermitian eigenvalues.
   * Pinned Mathlib supplies `Finset.card_union_of_disjoint`,
     `Matrix.rank_of_isUnit`, and `Fintype.card_sum`.
   * Repository search found no existing theorem identifying the exact
     positive and negative inertia of the zero-scale point-gap localizer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix Finset

namespace D5.S3.SpectralTopology.PointGapExactInertia

open RHLinalg
open D5.S3.SpectralTopology.FiniteSpectralLocalizer

noncomputable section

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- The strictly positive and strictly negative eigenvalue counts of a finite
Hermitian matrix add to its rank. -/
theorem posIndex_add_negIndex_eq_rank
    {K m : Type*} [RCLike K] [Fintype m] [DecidableEq m]
    {A : Matrix m m K} (hA : A.IsHermitian) :
    posIndex hA + negIndex hA = A.rank := by
  unfold posIndex negIndex
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hDisjoint :
      Disjoint
        (Finset.univ.filter fun i => 0 < hA.eigenvalues i)
        (Finset.univ.filter fun i => hA.eigenvalues i < 0) := by
    rw [Finset.disjoint_left]
    intro i hPositive hNegative
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      at hPositive hNegative
    exact (not_lt_of_ge hPositive.le) hNegative
  rw [← Finset.card_union_of_disjoint hDisjoint]
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hPositive | hNegative)
    · exact hPositive.ne'
    · exact hNegative.ne
  · intro hNonzero
    rcases lt_trichotomy (hA.eigenvalues i) 0 with
      hNegative | hZero | hPositive
    · exact Or.inr hNegative
    · exact False.elim (hNonzero hZero)
    · exact Or.inl hPositive

/-- A finite point gap makes the zero-scale localizer full rank on the doubled
carrier. -/
theorem zero_scale_localizer_rank_eq_card_of_point_gap
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z) :
    (finiteSpectralLocalizer X H 0 x z).rank =
      Fintype.card (n ⊕ n) := by
  exact Matrix.rank_of_isUnit _
    ((has_point_gap_iff_zero_scale_localizer_isUnit X H x z).1 hGap)

/-- Under a finite point gap, the positive and negative inertia counts of the
zero-scale localizer both equal the cardinality of the original carrier. -/
theorem zero_scale_localizer_inertia_of_point_gap
    (X H : Matrix n n ℂ) (x : ℝ) (z : ℂ)
    (hGap : HasPointGap H z) :
    posIndex
        (finite_spectral_localizer_zero_scale_isHermitian X H x z) =
        Fintype.card n ∧
      negIndex
        (finite_spectral_localizer_zero_scale_isHermitian X H x z) =
        Fintype.card n := by
  let hLocalizer :=
    finite_spectral_localizer_zero_scale_isHermitian X H x z
  have hBalance :
      posIndex hLocalizer = negIndex hLocalizer := by
    simpa only [hLocalizer] using
      zero_scale_localizer_posIndex_eq_negIndex X H x z
  have hTotal :
      posIndex hLocalizer + negIndex hLocalizer =
        2 * Fintype.card n := by
    calc
      posIndex hLocalizer + negIndex hLocalizer =
          (finiteSpectralLocalizer X H 0 x z).rank :=
        posIndex_add_negIndex_eq_rank hLocalizer
      _ = Fintype.card (n ⊕ n) :=
        zero_scale_localizer_rank_eq_card_of_point_gap X H x z hGap
      _ = 2 * Fintype.card n := by
        rw [Fintype.card_sum, two_mul]
  have hDouble :
      posIndex hLocalizer + posIndex hLocalizer =
        2 * Fintype.card n := by
    calc
      posIndex hLocalizer + posIndex hLocalizer =
          posIndex hLocalizer + negIndex hLocalizer :=
        congrArg (fun count : ℕ => posIndex hLocalizer + count) hBalance
      _ = 2 * Fintype.card n := hTotal
  have hPositive :
      posIndex hLocalizer = Fintype.card n := by
    apply Nat.mul_left_cancel zero_lt_two
    simpa only [two_mul] using hDouble
  have hNegative :
      negIndex hLocalizer = Fintype.card n :=
    hBalance.symm.trans hPositive
  simpa only [hLocalizer] using And.intro hPositive hNegative

#print axioms posIndex_add_negIndex_eq_rank
#print axioms zero_scale_localizer_rank_eq_card_of_point_gap
#print axioms zero_scale_localizer_inertia_of_point_gap

end

end D5.S3.SpectralTopology.PointGapExactInertia
