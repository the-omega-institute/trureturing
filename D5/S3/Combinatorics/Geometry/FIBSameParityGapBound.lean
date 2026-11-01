/- GID: D5/S3/Combinatorics/Geometry/FIBSameParityGapBound
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/FIBSameParityGapBound
   mirror-E: none(waiver:finite-count-input-is-external)
   anchors: []
   utility: none
   digest: Four cycle gaps have exact parity penalty six; negative deficits force strict bounds. -/

import Mathlib

/-! Four-gap parity and same-family deficit arithmetic for the FIB polygon bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.FIBSameParityGapBound

/-- The independent-set contribution of a gap of length `g` after removing its
    two endpoint centres. -/
def gapPenalty (g : ℕ) : ℕ := (g - 2) / 2

/-- Four gap penalties on a twenty-cycle are determined by the gap parities. -/
theorem four_gap_penalty_sum
    (g₁ g₂ g₃ g₄ : ℕ)
    (h₁ : 2 ≤ g₁) (h₂ : 2 ≤ g₂) (h₃ : 2 ≤ g₃) (h₄ : 2 ≤ g₄)
    (hsum : g₁ + g₂ + g₃ + g₄ = 20) :
    gapPenalty g₁ + gapPenalty g₂ + gapPenalty g₃ + gapPenalty g₄ =
      6 - ((g₁ % 2) + (g₂ % 2) + (g₃ % 2) + (g₄ % 2)) / 2 := by
  simp only [gapPenalty]
  omega

/-- The maximal six-unit carrier occurs exactly when all four cycle gaps are even. -/
theorem four_gap_penalty_eq_six_iff
    (g₁ g₂ g₃ g₄ : ℕ)
    (h₁ : 2 ≤ g₁) (h₂ : 2 ≤ g₂) (h₃ : 2 ≤ g₃) (h₄ : 2 ≤ g₄)
    (hsum : g₁ + g₂ + g₃ + g₄ = 20) :
    gapPenalty g₁ + gapPenalty g₂ + gapPenalty g₃ + gapPenalty g₄ = 6 ↔
      g₁ % 2 = 0 ∧ g₂ % 2 = 0 ∧ g₃ % 2 = 0 ∧ g₄ % 2 = 0 := by
  rw [four_gap_penalty_sum g₁ g₂ g₃ g₄ h₁ h₂ h₃ h₄ hsum]
  omega

/-- A same-family deficit estimate with a negative right side forces strict
    separation of the family cardinality from its reference level. -/
theorem same_family_strict_bound_of_negative_deficit
    {F L h G₁ G₂ G₃ : ℤ}
    (hbound : 2 * (F - L) ≤ h - 6 - G₁ - G₂ - G₃)
    (hnegative : h - 6 - G₁ - G₂ - G₃ < 0) :
    F < L := by
  linarith

/- The exact n=20 all-one-parity arithmetic application is kept as a
   compile-time check.  Its finite capacity and stability inequalities are
   supplied by the ordinary-count proof; this check introduces no new
   scenario-specific declaration. -/
example (F : ℤ)
    (hbound :
      2 * (F - 69753940) ≤
        8464690 - 6 - 3784063 - 2 * 2773974) :
    F < 69753940 := by
  have hbound' :
      2 * (F - 69753940 : ℤ) ≤
        (8464690 : ℤ) - 6 - 3784063 - 2773974 - 2773974 := by
    norm_num at hbound ⊢
    exact hbound
  exact same_family_strict_bound_of_negative_deficit
    (h := 8464690) (G₁ := 3784063) (G₂ := 2773974) (G₃ := 2773974)
    hbound' (by norm_num)

end D5.S3.Combinatorics.Geometry.FIBSameParityGapBound
