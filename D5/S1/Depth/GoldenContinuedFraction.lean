/- GID: D5/S1/Depth/GoldenContinuedFraction
   generality: I
   mirror-B: D5/B/S1/Depth/GoldenContinuedFraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mathlib's computed continued fraction of the golden ratio has every coefficient one. -/

import Mathlib

namespace D5.S1.Depth.GoldenContinuedFraction

private theorem goldenRatio_floor : ⌊Real.goldenRatio⌋ = 1 := by
  rw [Int.floor_eq_iff]
  norm_num only [Int.cast_one, Int.cast_add]
  exact ⟨le_of_lt Real.one_lt_goldenRatio, Real.goldenRatio_lt_two⟩

private theorem goldenRatio_fract : Int.fract Real.goldenRatio = Real.goldenRatio - 1 := by
  simp [Int.fract, goldenRatio_floor]

private theorem goldenRatio_fract_ne_zero : Int.fract Real.goldenRatio ≠ 0 := by
  rw [goldenRatio_fract]
  exact sub_ne_zero.mpr (ne_of_gt Real.one_lt_goldenRatio)

private theorem goldenRatio_inv_fract :
    (Int.fract Real.goldenRatio)⁻¹ = Real.goldenRatio := by
  rw [goldenRatio_fract]
  apply inv_eq_of_mul_eq_one_right
  nlinarith [Real.goldenRatio_sq]

/-- The generalized continued fraction computed by mathlib for the golden ratio has head one
and every numerator-denominator pair equal to `(1, 1)`. -/
theorem golden_ratio_continued_fraction :
    (GenContFract.of Real.goldenRatio).h = 1 ∧
      ∀ n, (GenContFract.of Real.goldenRatio).s.get? n = some ⟨1, 1⟩ := by
  constructor
  · rw [GenContFract.of_h_eq_floor]
    exact_mod_cast goldenRatio_floor
  · intro n
    induction n with
    | zero =>
        simpa [Stream'.Seq.head, goldenRatio_inv_fract, goldenRatio_floor] using
          GenContFract.of_s_head goldenRatio_fract_ne_zero
    | succ n ih =>
        rw [GenContFract.of_s_succ, goldenRatio_inv_fract]
        exact ih

end D5.S1.Depth.GoldenContinuedFraction
