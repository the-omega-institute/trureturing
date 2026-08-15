/- GID: D5/S3/Zeros/ShiftOperators/BackwardShiftCoisometry
   generality: I
   mirror-B: D5/B/S3/Zeros/ShiftOperators/BackwardShiftCoisometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete the backward shift as a coisometry with an isometric right inverse. -/

import D5.S3.Zeros.ShiftOperators.BackwardShiftOperator

namespace D5.S3.Zeros.ShiftOperators.BackwardShiftCoisometry

open D5.S1.Digit
open D5.S3.Weil.SpectralHilbert
open D5.S3.Zeros.SpectralShift
open D5.S3.Zeros.ShiftOperators.BackwardShiftOperator

noncomputable local instance : DecidableEq PrimeAxisTable := Classical.decEq _

/-- The zero-extended forward translation is a right inverse of the backward shift. -/
theorem backward_shift_comp_forward_translation (u : PrimeAxisTable)
    (x : ZetaHilbertSpace) :
    backwardShiftCLM u (forwardTranslationCLM u x) = x := by
  ext a
  change Function.extend (fun b : PrimeAxisTable => normalizedTableAdd b u) x 0
      (normalizedTableAdd a u) = x a
  exact (normalizedTableAdd_right_injective u).extend_apply x 0 a

/-- Every vector has a zero-extended preimage under the backward shift. -/
theorem backward_shift_surjective (u : PrimeAxisTable) :
    Function.Surjective (backwardShiftCLM u) := by
  intro x
  exact ⟨forwardTranslationCLM u x, backward_shift_comp_forward_translation u x⟩

/-- Zero-extension along multiplicative translation preserves the Hilbert norm exactly. -/
theorem forward_translation_norm_eq (u : PrimeAxisTable) (x : ZetaHilbertSpace) :
    ‖forwardTranslationCLM u x‖ = ‖x‖ := by
  apply le_antisymm
  · change ‖forwardTranslationLinearMap u x‖ ≤ ‖x‖
    exact forwardTranslationLinearMap_norm_nonincreasing u x
  · calc
      ‖x‖ = ‖backwardShiftCLM u (forwardTranslationCLM u x)‖ := by
        rw [backward_shift_comp_forward_translation]
      _ ≤ ‖forwardTranslationCLM u x‖ := by
        change ‖backwardShiftLinearMap u (forwardTranslationCLM u x)‖ ≤ _
        exact backwardShiftLinearMap_norm_nonincreasing u (forwardTranslationCLM u x)

/-- The backward shift is a coisometry and has operator norm exactly one. -/
theorem backward_shift_operator_norm_eq_one (u : PrimeAxisTable) :
    ‖backwardShiftCLM u‖ = 1 := by
  apply le_antisymm (backward_shift_operator_norm_le_one u)
  let e : ZetaHilbertSpace := lp.single 2 u (1 : ℂ)
  have he : ‖e‖ = 1 := by
    simp [e]
  calc
    1 = ‖backwardShiftCLM u (forwardTranslationCLM u e)‖ := by
      rw [backward_shift_comp_forward_translation, he]
    _ ≤ ‖backwardShiftCLM u‖ :=
      (backwardShiftCLM u).unit_le_opNorm _ (by
        rw [forward_translation_norm_eq, he])

end D5.S3.Zeros.ShiftOperators.BackwardShiftCoisometry
