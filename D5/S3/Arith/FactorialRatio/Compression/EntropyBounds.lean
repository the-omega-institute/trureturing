/- GID: D5/S3/Arith/FactorialRatio/Compression/EntropyBounds
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/Compression/EntropyBounds
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.BinaryEntropy]
   utility: none
   digest: A quartic entropy majorant bounds the optimized profile below the logarithmic threshold. -/

import D5.S3.Arith.FactorialRatio.Compression.EntropyProfile
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A quartic correction sharpens the average binary-entropy bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.Compression.EntropyBounds

open Real Set
open D5.S3.Arith.FactorialRatio.Compression.EntropyProfile

private def corrected (v : ℝ) : ℝ :=
  binEntropy v + 2 * (v - 1 / 2) ^ 2 + 4 / 3 * (v - 1 / 2) ^ 4

private theorem corrected_concave : ConcaveOn ℝ (Icc 0 1) corrected := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun v =>
      log (1 - v) - log v + 4 * (v - 1 / 2) + 16 / 3 * (v - 1 / 2) ^ 3)
    (f'' := fun v => -1 / (1 - v) - 1 / v + 4 + 16 * (v - 1 / 2) ^ 2)
    (convex_Icc 0 1)
  · unfold corrected
    fun_prop
  · intro v hv
    simp only [interior_Icc, Set.mem_Ioo] at hv
    have hd := ((hasDerivAt_binEntropy hv.1.ne' (ne_of_lt hv.2)).add
      ((((hasDerivAt_id v).sub_const (1 / 2)).pow 2).const_mul 2)).add
      ((((hasDerivAt_id v).sub_const (1 / 2)).pow 4).const_mul (4 / 3))
    convert hd.hasDerivWithinAt using 1
    · funext y
      dsimp [corrected] <;> ring
    · dsimp <;> ring
  · intro v hv
    simp only [interior_Icc, Set.mem_Ioo] at hv
    have hd := ((((((hasDerivAt_id v).const_sub 1).log
        (sub_pos.mpr hv.2).ne').sub (Real.hasDerivAt_log hv.1.ne')).add
      (((hasDerivAt_id v).sub_const (1 / 2)).const_mul 4)).add
      ((((hasDerivAt_id v).sub_const (1 / 2)).pow 3).const_mul (16 / 3)))
    convert hd.hasDerivWithinAt using 1
    · funext y
      dsimp <;> ring
    · dsimp <;> ring
  · intro v hv
    simp only [interior_Icc, Set.mem_Ioo] at hv
    have hden : 0 < v * (1 - v) := mul_pos hv.1 (sub_pos.mpr hv.2)
    have heq : -1 / (1 - v) - 1 / v + 4 + 16 * (v - 1 / 2) ^ 2 =
        -((2 * v - 1) ^ 4) / (v * (1 - v)) := by
      field_simp [hv.1.ne', (sub_pos.mpr hv.2).ne'] <;> ring
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hden.le

private theorem entropy_quartic {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    binEntropy v ≤ log 2 - (2 * v - 1) ^ 2 / 2 - (2 * v - 1) ^ 4 / 12 := by
  have h := corrected_concave.2 ⟨hv, hv1⟩
    (show 1 - v ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  have hm : (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • (1 - v) = 2⁻¹ := by
    simp only [smul_eq_mul]; ring
  rw [hm] at h
  simp only [corrected, binEntropy_one_sub, binEntropy_two_inv, smul_eq_mul] at h
  nlinarith

private theorem integral_quartic_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    -(161 / 288 : ℝ) ≤ entropyIntegral t := by
  let g : ℝ → ℝ := fun u =>
    log 2 - (2 * (t * u) - 1) ^ 2 / 2 - (2 * (t * u) - 1) ^ 4 / 12
  have hint : IntervalIntegrable g MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous g).intervalIntegrable _ _
  have hp : (∫ u in (0 : ℝ)..1, g u) =
      log 2 - 7 / 12 + 4 / 3 * t - 4 / 3 * t ^ 2 + 2 / 3 * t ^ 3 -
        4 / 15 * t ^ 4 := by
    let F : ℝ → ℝ := fun u => (log 2 - 7 / 12) * u + 4 / 3 * t * u ^ 2 -
      4 / 3 * t ^ 2 * u ^ 3 + 2 / 3 * t ^ 3 * u ^ 4 - 4 / 15 * t ^ 4 * u ^ 5
    have hF (u : ℝ) : HasDerivAt F (g u) u := by
      convert ((((((hasDerivAt_id u).const_mul (log 2 - 7 / 12)).add
        (((hasDerivAt_id u).pow 2).const_mul (4 / 3 * t))).sub
        (((hasDerivAt_id u).pow 3).const_mul (4 / 3 * t ^ 2))).add
        (((hasDerivAt_id u).pow 4).const_mul (2 / 3 * t ^ 3))).sub
        (((hasDerivAt_id u).pow 5).const_mul (4 / 15 * t ^ 4))) using 1
      · funext y
        dsimp [F] <;> ring
      · dsimp [g] <;> ring
    simpa [F] using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u) hint
  have hm := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) (by norm_num)
    ((by fun_prop : Continuous (fun u : ℝ => binEntropy (t * u))).intervalIntegrable _ _) hint
    (fun u hu => entropy_quartic (mul_nonneg ht hu.1)
      ((mul_le_mul_of_nonneg_right ht1 hu.1).trans (by simpa using hu.2)))
  rw [hp] at hm
  have hlog : log 2 ≤ (25 / 36 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hsos : (1 / 9 : ℝ) + 4 / 3 * t - 4 / 3 * t ^ 2 + 2 / 3 * t ^ 3 -
      4 / 15 * t ^ 4 = 161 / 288 - (1 - t) ^ 2 / 60 -
        (4 * t - 3) ^ 2 * (2 * (2 * t - 1) ^ 2 + 21) / 480 := by ring
  have hP : log 2 - 7 / 12 + 4 / 3 * t - 4 / 3 * t ^ 2 + 2 / 3 * t ^ 3 -
      4 / 15 * t ^ 4 ≤ (161 / 288 : ℝ) := by
    have hfirst : (0 : ℝ) ≤ (1 - t) ^ 2 / 60 := by positivity
    have hsecond : (0 : ℝ) ≤
        (4 * t - 3) ^ 2 * (2 * (2 * t - 1) ^ 2 + 21) / 480 := by positivity
    linarith
  rw [entropyIntegral, intervalIntegral.integral_neg]
  linarith

/-- The optimized negative entropy average is bounded by `161/288`, strictly
below the logarithmic comparison constant and the Euler--Mascheroni constant. -/
theorem sharp_entropy_profile_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    -(161 / 288 : ℝ) ≤ entropyIntegral t ∧
      (161 / 288 : ℝ) < 2 * log 2 - 3 / 4 * log 3 ∧
      2 * log 2 - 3 / 4 * log 3 < (563 / 1000 : ℝ) ∧
      (563 / 1000 : ℝ) < Real.eulerMascheroniConstant := by
  refine ⟨integral_quartic_bound ht ht1, ?_, ?_, ?_⟩
  · linarith [Real.log_two_gt_d9, Real.log_three_lt_d9]
  · linarith [Real.log_two_lt_d9, Real.log_three_gt_d9]
  · have h := D5.S3.Arith.GoldenResource.RobinRationalBasis.eulerMascheroni_decimal_bounds
    linarith [h.1]

end D5.S3.Arith.FactorialRatio.Compression.EntropyBounds
