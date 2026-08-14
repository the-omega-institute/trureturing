/- GID: D5/S3/Zeros/Symmetry/ReflectionFixedPointContrast
   generality: I
   mirror-B: D5/B/S3/Zeros/Symmetry/ReflectionFixedPointContrast
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Plain reflection fixes one point, while conjugate reflection fixes the critical line. -/

/- Library-search audit trail (2026-08-14):
   * Searches for `reflection_fixed_iff`, reflection fixed-set singleton shapes,
     and `one_sub_eq_self` found no exact theorem in pinned Mathlib or D5.
   * Exact frozen D5 dependency hits: `ReflectionLedger.reflection` supplies
     the required plain reflection, and `midline_dual_characterization`
     supplies the mirror fixed-set equality with the critical line.
-/

import D5.S3.Midline.DualCharacterization

namespace D5.S3.Zeros.Symmetry.ReflectionFixedPointContrast

open D5.S3.Midline.DualCharacterization
open D5.S3.Weil.Convention D5.S3.Weil.ReflectionLedger

/-- Plain reflection about one half has exactly one fixed point. -/
theorem reflection_fixed_iff (s : ℂ) :
    reflection s = s ↔ s = (1 / 2 : ℂ) := by
  rw [reflection]
  constructor
  · intro h
    linear_combination (-1 / 2) * h
  · rintro rfl
    norm_num

/-- Plain reflection fixes a singleton, whereas conjugate reflection fixes
the entire critical line. -/
theorem reflection_mirror_fixed_locus_contrast :
    {s : ℂ | reflection s = s} = {(1 / 2 : ℂ)} ∧
      {s : ℂ | mirror s = s} =
        {s : ℂ | s.re = criticalAbscissa} := by
  constructor
  · ext s
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, reflection_fixed_iff]
  · exact
      (midline_dual_characterization (Nat.castAddMonoidHom ℝ)
        ⟨1, by norm_num⟩).2

-- The fixed-point carrier is inhabited independently of either theorem.
example : ℂ := 0

end D5.S3.Zeros.Symmetry.ReflectionFixedPointContrast
