/- GID: D5/S1/Depth/ContinuedFractions/PeriodicThreeComplement
   generality: I
   mirror-B: D5/B/S1/Depth/ContinuedFractions/PeriodicThreeComplement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The period-three tail and its [0;1,2] prefix are complementary. -/

import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.Tactic

/- Mathlib search found the generic continued-fraction computation lemmas
   `GenContFract.of_h_eq_floor`, `GenContFract.of_s_head`, and
   `GenContFract.of_s_succ`, which are applied below. No pinned Mathlib or
   Loogle declaration states this period-three expansion or complement identity. -/

namespace D5.S1.Depth.ContinuedFractions.PeriodicThreeComplement

/-- For `x = (sqrt 13 - 3) / 2`, Mathlib's computed continued fraction is
`[0; 3, 3, ...]`, and adjoining the prefix `[0; 1, 2]` produces `1 - x`. -/
theorem periodic_three_continued_fraction_complement :
    let x : ℝ := (Real.sqrt 13 - 3) / 2
    (GenContFract.of x).h = 0 ∧
      (∀ n, (GenContFract.of x).s.get? n = some ⟨1, 3⟩) ∧
      1 / (1 + 1 / (2 + x)) + x = 1 := by
  let x : ℝ := (Real.sqrt 13 - 3) / 2
  have hsqrt_sq : (Real.sqrt 13) ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 13 := Real.sqrt_nonneg 13
  have hx_pos : 0 < x := by
    dsimp [x]
    nlinarith
  have hx_lt_one : x < 1 := by
    dsimp [x]
    nlinarith
  have hx_floor : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hx_pos.le, hx_lt_one⟩
  have hx_fract : Int.fract x = x := by
    rw [Int.fract, hx_floor, Int.cast_zero, sub_zero]
  have hx_fract_ne : Int.fract x ≠ 0 := by
    rw [hx_fract]
    exact ne_of_gt hx_pos
  have hx_mul : x * (3 + x) = 1 := by
    dsimp [x]
    nlinarith
  have hx_inv : x⁻¹ = 3 + x :=
    inv_eq_of_mul_eq_one_right hx_mul
  have hshift_floor : ⌊(3 : ℝ) + x⌋ = 3 := by
    rw [Int.floor_eq_iff]
    norm_num only [Int.cast_ofNat, Int.cast_add]
    exact ⟨by linarith, by linarith⟩
  have hshift_fract : Int.fract ((3 : ℝ) + x) = x := by
    rw [Int.fract, hshift_floor]
    norm_num
  have hshift_fract_ne : Int.fract ((3 : ℝ) + x) ≠ 0 := by
    rw [hshift_fract]
    exact ne_of_gt hx_pos
  have hshift_sequence :
      ∀ n, (GenContFract.of ((3 : ℝ) + x)).s.get? n = some ⟨1, 3⟩ := by
    intro n
    induction n with
    | zero =>
        simpa [Stream'.Seq.head, hshift_fract, hx_inv, hshift_floor] using
          GenContFract.of_s_head hshift_fract_ne
    | succ n ih =>
        rw [GenContFract.of_s_succ, hshift_fract, hx_inv]
        exact ih
  have hx_sequence : ∀ n, (GenContFract.of x).s.get? n = some ⟨1, 3⟩ := by
    intro n
    cases n with
    | zero =>
        simpa [Stream'.Seq.head, hx_fract, hx_inv, hshift_floor] using
          GenContFract.of_s_head hx_fract_ne
    | succ n =>
        rw [GenContFract.of_s_succ, hx_fract, hx_inv]
        exact hshift_sequence n
  have hx_head : (GenContFract.of x).h = 0 := by
    rw [GenContFract.of_h_eq_floor]
    exact_mod_cast hx_floor
  have hcomplement : 1 / (1 + 1 / (2 + x)) + x = 1 := by
    have htwo_pos : 0 < 2 + x := by linarith
    have houter_pos : 0 < 1 + 1 / (2 + x) := by positivity
    field_simp [ne_of_gt htwo_pos, ne_of_gt houter_pos]
    nlinarith [hx_mul]
  exact ⟨hx_head, hx_sequence, hcomplement⟩

#print axioms periodic_three_continued_fraction_complement

end D5.S1.Depth.ContinuedFractions.PeriodicThreeComplement
