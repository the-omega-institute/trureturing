/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular.SLnUnitriangular
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! An actual entry-coordinate bijection for the accepted full upper
unitriangular subgroup, over every field and rank. -/
namespace NikolovSegal.SLnSylow
open Matrix
open NikolovSegal.SLnNormalizer
universe u
variable {F : Type u} [Field F] {n : ℕ}

/-- One free coordinate for each entry strictly above the diagonal. -/
abbrev UpperEntry (n : ℕ) := Σ c : Fin n, Fin c.val

/-- Literal unitriangular matrix with the prescribed free upper entries. -/
def upperMatrix (f : UpperEntry n → F) : Matrix (Fin n) (Fin n) F :=
  fun r c => if h : r.val < c.val then f ⟨c,⟨r.val,h⟩⟩ else (1 : Matrix (Fin n) (Fin n) F) r c

theorem upperMatrix_triangular (f : UpperEntry n → F) : (upperMatrix f).IsUpperTriangular := by
  intro r c hcr
  change c.val < r.val at hcr
  have hrc : ¬ r.val < c.val := by omega
  have hne : r ≠ c := fun he => by subst c; exact lt_irrefl _ hcr
  simp [upperMatrix, hrc, hne]

theorem upperMatrix_diag (f : UpperEntry n → F) (r : Fin n) : upperMatrix f r r = 1 := by
  simp [upperMatrix]

/-- Every assignment of free entries is an actual determinant-one Uplus element. -/
def upperChart (f : UpperEntry n → F) : Uplus n F :=
  ⟨⟨upperMatrix f, by
      rw [Matrix.det_of_isUpperTriangular (upperMatrix_triangular f)]
      simp [upperMatrix_diag]⟩,
    ⟨fun r c hcr => upperMatrix_triangular f hcr, upperMatrix_diag f⟩⟩

/-- Actual coordinate equivalence, not a group-order or coverage hypothesis. -/
def upperCoordinatesEquiv (n : ℕ) (F : Type u) [Field F] : Uplus n F ≃ (UpperEntry n → F) where
  toFun g := fun a => g.val.val ⟨a.2.val, a.2.isLt.trans a.1.isLt⟩ a.1
  invFun := upperChart
  left_inv := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    ext r c
    change upperMatrix (fun a => g.val.val ⟨a.2.val,a.2.isLt.trans a.1.isLt⟩ a.1) r c = g.val.val r c
    by_cases hrc : r.val < c.val
    · simp only [upperMatrix, dif_pos hrc]
    · by_cases he : r = c
      · subst c
        simp [upperMatrix, g.property.2 r]
      · have hcr : c.val < r.val := by
          have hne : r.val ≠ c.val := fun h => he (Fin.ext h)
          omega
        simp [upperMatrix, hrc, he, g.property.1 r c hcr]
  right_inv := by
    intro f
    funext a
    rcases a with ⟨c,r⟩
    change upperMatrix f ⟨r.val,r.isLt.trans c.isLt⟩ c = f ⟨c,r⟩
    simp only [upperMatrix, dif_pos r.isLt]

/-- Exact cardinality as the sum of column dimensions, valid also in ranks0/1. -/
theorem card_Uplus_sum [Fintype F] (n : ℕ) :
    Nat.card (Uplus n F) = (Fintype.card F) ^ (∑ c : Fin n, c.val) := by
  rw [Nat.card_congr (upperCoordinatesEquiv n F), Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_fin]

/-- The literal free-entry dimension n*(n-1)/2. -/
theorem card_Uplus [Fintype F] (n : ℕ) :
    Nat.card (Uplus n F) = (Fintype.card F) ^ (n*(n-1)/2) := by
  rw [card_Uplus_sum]
  have hs : (∑ c : Fin n, c.val) = n*(n-1)/2 :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n).trans (Finset.sum_range_id n)
  rw [hs]

end NikolovSegal.SLnSylow
