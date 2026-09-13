/- GID: D5/S1/Recurrence/RotationExplicitHittingBound
   generality: G
   mirror-B: D5/B/S1/Recurrence/RotationExplicitHittingBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The floor mesh has a seam gap bounded by its mesh size. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S1.Recurrence.RotationExplicitHittingBound

/-- For a positive mesh size, the final seam gap of the floor mesh is between zero and one mesh step. -/
theorem floor_mesh_seam_gap_bounds (h : ℝ) (hh : 0 < h) :
    let M : ℤ := ⌊1 / h⌋
    0 ≤ 1 - (M : ℝ) * h ∧ 1 - (M : ℝ) * h ≤ h := by
  dsimp
  have hfloor : (⌊1 / h⌋ : ℝ) ≤ 1 / h := by
    exact_mod_cast (Int.floor_le (1 / h))
  have hlt : 1 / h < (⌊1 / h⌋ : ℝ) + 1 := by
    exact_mod_cast (Int.lt_floor_add_one (1 / h))
  have hmul : (⌊1 / h⌋ : ℝ) * h ≤ 1 := by
    calc
      (⌊1 / h⌋ : ℝ) * h ≤ (1 / h) * h :=
        mul_le_mul_of_nonneg_right hfloor (le_of_lt hh)
      _ = 1 := by field_simp [ne_of_gt hh]
  have hmul' : 1 < ((⌊1 / h⌋ : ℝ) + 1) * h := by
    calc
      1 = (1 / h) * h := by field_simp [ne_of_gt hh]
      _ < ((⌊1 / h⌋ : ℝ) + 1) * h :=
        mul_lt_mul_of_pos_right hlt hh
  constructor <;> linarith

end D5.S1.Recurrence.RotationExplicitHittingBound
