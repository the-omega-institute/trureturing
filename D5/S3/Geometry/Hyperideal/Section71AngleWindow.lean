/- GID: D5/S3/Geometry/Hyperideal/Section71AngleWindow
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/Section71AngleWindow
   mirror-E: none(waiver:section-71-angle-window)
   anchors: []
   utility: none
   digest: A short-axis response angle lies strictly between pi over three and pi over two. -/

/-
proof_shape: middle_angle_window: content
admission_basis: escape-witness.
escape_witness: htan_beta_sq, the strict tangent-square estimate for the
arctangent response, is derived from the half-angle and cotangent hypotheses
and is not an instance of an imported theorem.
Escape audit unfinished: issue #10609 tracks the missing faithful four-slot
registration for the paired hyperideal angle-response family; this local
angle-window theorem has no declared_validated Reg mirror yet.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! The strict middle-angle window used by the Section 71 short-axis branch. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Geometry.Hyperideal.Section71AngleWindow

def middleAngle (h Q theta : ℝ) : ℝ :=
  Real.arctan
    (Real.sqrt ((h ^ 2 - 1) / (Q + h ^ 2)) * Real.cot (theta / 2))

theorem middle_angle_window {h Q theta : ℝ}
    (hh : 1 < h)
    (hQh : Q ≤ h)
    (htheta_pos : 0 < theta)
    (htheta_lt_pi : theta < Real.pi)
    (htan_le : Real.tan (theta / 2) ≤ (1 : ℝ) / 2)
    (hQcot : (Real.cot (theta / 2)) ^ 2 < Q) :
    Real.pi / 3 < middleAngle h Q theta ∧
      middleAngle h Q theta < Real.pi / 2 := by
  have hhalf_sin : 0 < Real.sin (theta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [htheta_pos])
      (by linarith [htheta_lt_pi, Real.pi_pos])
  have hhalf_cos : 0 < Real.cos (theta / 2) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [htheta_lt_pi]⟩
  have htan_pos : 0 < Real.tan (theta / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hhalf_sin hhalf_cos
  have hcot : Real.cot (theta / 2) = 1 / Real.tan (theta / 2) := by
    rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos]
    field_simp [hhalf_sin.ne', hhalf_cos.ne']
  have hcot_pos : 0 < Real.cot (theta / 2) := by
    rw [hcot]
    positivity
  have hcot_ge_two : 2 ≤ Real.cot (theta / 2) := by
    rw [hcot]
    apply (le_div_iff₀ htan_pos).2
    nlinarith [htan_le]
  have hcot_sq_ge_four : 4 ≤ (Real.cot (theta / 2)) ^ 2 := by
    nlinarith [sq_nonneg (Real.cot (theta / 2) - 2)]
  have hQ_four : 4 < Q := lt_of_le_of_lt hcot_sq_ge_four hQcot
  have hQ_pos : 0 < Q := by linarith
  have hden_pos : 0 < Q + h ^ 2 := by positivity
  have hnum_pos : 0 < h ^ 2 - 1 := by nlinarith
  let lambda : ℝ := Real.sqrt ((h ^ 2 - 1) / (Q + h ^ 2))
  have hlambda_pos : 0 < lambda := by
    dsimp [lambda]
    exact Real.sqrt_pos.2 (div_pos hnum_pos hden_pos)
  have hlambda_sq : lambda ^ 2 = (h ^ 2 - 1) / (Q + h ^ 2) := by
    dsimp [lambda]
    rw [Real.sq_sqrt]
    exact (div_nonneg hnum_pos.le hden_pos.le)
  have hsq : 0 ≤ (h - Q) * (h + Q) := by
    exact mul_nonneg (sub_nonneg.mpr hQh) (by nlinarith [hQ_pos, hQh])
  have hcross : (Q - 1) * (Q + h ^ 2) ≤ Q * (h ^ 2 - 1) := by
    nlinarith [hsq]
  have hratio : (Q - 1) / Q ≤ (h ^ 2 - 1) / (Q + h ^ 2) := by
    apply (div_le_div_iff₀ hQ_pos hden_pos).2
    simpa [mul_comm] using hcross
  have hlambda_lower : 1 - 1 / Q ≤ lambda ^ 2 := by
    rw [hlambda_sq]
    calc
      1 - 1 / Q = (Q - 1) / Q := by field_simp
      _ ≤ (h ^ 2 - 1) / (Q + h ^ 2) := hratio
  have hQmul : 1 < Q * (Real.tan (theta / 2)) ^ 2 := by
    have hmul := mul_lt_mul_of_pos_right hQcot (sq_pos_of_pos htan_pos)
    rw [hcot] at hmul
    have hone : (1 / Real.tan (theta / 2)) ^ 2 *
        Real.tan (theta / 2) ^ 2 = 1 := by
      field_simp [htan_pos.ne']
    rw [hone] at hmul
    exact hmul
  have hinv_lt : 1 / Q < (Real.tan (theta / 2)) ^ 2 := by
    apply (div_lt_iff₀ hQ_pos).2
    nlinarith [hQmul]
  have hlambda_tan_gap :
      1 - (Real.tan (theta / 2)) ^ 2 < lambda ^ 2 := by
    have hgap : 1 - (Real.tan (theta / 2)) ^ 2 < 1 - 1 / Q := by
      linarith
    exact lt_of_lt_of_le hgap hlambda_lower
  have htan_sq_bound : 3 ≤ 1 / (Real.tan (theta / 2)) ^ 2 - 1 := by
    have hfour : 4 ≤ 1 / (Real.tan (theta / 2)) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos htan_pos)).2
      nlinarith [htan_le]
    linarith
  have htan_beta_sq :
      3 < (Real.tan (Real.arctan (lambda * Real.cot (theta / 2)))) ^ 2 := by
    rw [Real.tan_arctan, hcot]
    have htan_sq_pos : 0 < (Real.tan (theta / 2)) ^ 2 := sq_pos_of_pos htan_pos
    have hmul_gap :
        (1 - (Real.tan (theta / 2)) ^ 2) /
            (Real.tan (theta / 2)) ^ 2 < lambda ^ 2 /
            (Real.tan (theta / 2)) ^ 2 := by
      apply (div_lt_iff₀ htan_sq_pos).2
      calc
        1 - (Real.tan (theta / 2)) ^ 2 < lambda ^ 2 := hlambda_tan_gap
        _ = (lambda ^ 2 / (Real.tan (theta / 2)) ^ 2) *
              (Real.tan (theta / 2)) ^ 2 := by
          field_simp [htan_pos.ne']
    have hrew :
        (1 - (Real.tan (theta / 2)) ^ 2) /
            (Real.tan (theta / 2)) ^ 2 =
          1 / (Real.tan (theta / 2)) ^ 2 - 1 := by
      field_simp [htan_pos.ne']
    rw [hrew] at hmul_gap
    have hquot : 3 < lambda ^ 2 / (Real.tan (theta / 2)) ^ 2 :=
      lt_of_le_of_lt htan_sq_bound hmul_gap
    have hfinal : 3 < lambda ^ 2 * (1 / Real.tan (theta / 2)) ^ 2 := by
      calc
        3 < lambda ^ 2 / (Real.tan (theta / 2)) ^ 2 := hquot
        _ = lambda ^ 2 * (1 / Real.tan (theta / 2)) ^ 2 := by
          field_simp [htan_pos.ne']
    simpa [mul_pow] using hfinal
  have harg_pos : 0 < lambda * Real.cot (theta / 2) :=
    mul_pos hlambda_pos hcot_pos
  have hpi3 : Real.pi / 3 < Real.arctan (lambda * Real.cot (theta / 2)) := by
    have harg_sq : 3 < (lambda * Real.cot (theta / 2)) ^ 2 := by
      simpa [Real.tan_arctan] using htan_beta_sq
    have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
    have harg_gt : Real.sqrt 3 < lambda * Real.cot (theta / 2) := by
      by_contra hnot
      have hle : lambda * Real.cot (theta / 2) ≤ Real.sqrt 3 := le_of_not_gt hnot
      nlinarith [sq_nonneg (lambda * Real.cot (theta / 2) - Real.sqrt 3)]
    have hmono := Real.arctan_strictMono harg_gt
    simpa using hmono
  have hpi2 : Real.arctan (lambda * Real.cot (theta / 2)) < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  exact ⟨by simpa [middleAngle] using hpi3, by simpa [middleAngle] using hpi2⟩

#print axioms middle_angle_window

end D5.S3.Geometry.Hyperideal.Section71AngleWindow
