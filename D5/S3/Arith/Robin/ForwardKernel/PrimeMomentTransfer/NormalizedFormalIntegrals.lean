/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizedFormalIntegrals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform formal moment bounds yield weighted normalized integral bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.WeightedIntegralTools
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.NormalizationAlgebra

/-! Normalized integration of uniform formal moment errors. -/

open Set MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

theorem integrated_third_envelope (SS : Finset ℕ → ℝ) (N H B C E : ℝ)
    (w : ℝ → ℝ) (a b : Fin 3 → ℝ) (hN : 2 ≤ N) (hH : 0 < H)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hw : BVBound w B)
    (hf : ∀ x ∈ Icc N (2 * N), |Phi SS H (Real.log x) a b| ≤
      C * (E * (H * Real.log N) ^ (3 / 2 : ℝ) + H * (Real.log N) ^ 2)) :
    |(∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b) /
        (N * (H * Real.log N) ^ (3 / 2 : ℝ))| ≤
      C * B * (E + Real.sqrt (Real.log N / H)) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hB : 0 ≤ B := hw.2.2.1
  have hQ : 0 < (H * Real.log N) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos (mul_pos hH hL) _
  have hi := weighted_integral_uniform_bound N B _ w
    (fun x => Phi SS H (Real.log x) a b) hN0.le hB (by positivity)
    (fun x _ => bv_sup_bound w B hw (x / N)) hf
  rw [abs_div, abs_of_pos (mul_pos hN0 hQ)]
  calc
    _ ≤ (N * B * (C * (E * (H * Real.log N) ^ (3 / 2 : ℝ) +
        H * (Real.log N) ^ 2))) / (N * (H * Real.log N) ^ (3 / 2 : ℝ)) :=
      div_le_div_of_nonneg_right hi (mul_pos hN0 hQ).le
    _ = C * B * ((E * (H * Real.log N) ^ (3 / 2 : ℝ) +
        H * (Real.log N) ^ 2) / (H * Real.log N) ^ (3 / 2 : ℝ)) := by
      field_simp
    _ = _ := by rw [cubic_formal_ratio H (Real.log N) E hH hL]

theorem integrated_fourth_envelope (SS : Finset ℕ → ℝ) (N H B C E : ℝ)
    (w : ℝ → ℝ) (a b : Fin 4 → ℝ) (hN : 2 ≤ N) (hH : 0 < H)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hw : BVBound w B)
    (hf : ∀ x ∈ Icc N (2 * N),
      |Phi SS H (Real.log x) a b - H ^ 2 * (Real.log x - Real.log H) ^ 2 * W4 a b| ≤
        C * (E * H ^ 2 * (Real.log N) ^ 2 + H ^ 2 * Real.log N)) :
    |(∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b) /
        (N * (H * Real.log N) ^ 2) -
      (∫ x in N..2 * N, w (x / N) *
        (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) / N| ≤
      C * B * (E + 1 / Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hB : 0 ≤ B := hw.2.2.1
  have hQ : 0 < (H * Real.log N) ^ 2 := pow_pos (mul_pos hH hL) _
  have hi := formal_weight_integrable SS N H B w 4 a b hN hw
  have hp := ((polynomial_weight_integrable N hN B w hw
    ((Polynomial.X - Polynomial.C (Real.log H)) ^ 2)).mul_const (H ^ 2)).mul_const
      (W4 a b)
  have hj : IntervalIntegrable (fun x => w (x / N) *
      (H ^ 2 * (Real.log x - Real.log H) ^ 2 * W4 a b)) volume N (2 * N) := by
    convert hp using 1
    ext x
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    ring
  have hmain : (∫ x in N..2 * N, w (x / N) *
      (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) =
      (∫ x in N..2 * N, w (x / N) *
        (H ^ 2 * (Real.log x - Real.log H) ^ 2 * W4 a b)) / (H * Real.log N) ^ 2 := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro x _
    field_simp
  have heq : (∫ x in N..2 * N, w (x / N) * Phi SS H (Real.log x) a b) /
        (N * (H * Real.log N) ^ 2) -
      (∫ x in N..2 * N, w (x / N) *
        (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) / N =
      (∫ x in N..2 * N, w (x / N) *
        (Phi SS H (Real.log x) a b -
          H ^ 2 * (Real.log x - Real.log H) ^ 2 * W4 a b)) /
        (N * (H * Real.log N) ^ 2) := by
    rw [hmain]
    have hs := intervalIntegral.integral_sub hi hj
    simp_rw [← mul_sub] at hs
    rw [hs]
    ring
  have hb := weighted_integral_uniform_bound N B _ w
    (fun x => Phi SS H (Real.log x) a b -
      H ^ 2 * (Real.log x - Real.log H) ^ 2 * W4 a b) hN0.le hB (by positivity)
    (fun x _ => bv_sup_bound w B hw (x / N)) hf
  rw [heq, abs_div, abs_of_pos (mul_pos hN0 hQ)]
  calc
    _ ≤ (N * B * (C * (E * H ^ 2 * (Real.log N) ^ 2 + H ^ 2 * Real.log N))) /
        (N * (H * Real.log N) ^ 2) :=
      div_le_div_of_nonneg_right hb (mul_pos hN0 hQ).le
    _ = C * B * ((E * H ^ 2 * (Real.log N) ^ 2 + H ^ 2 * Real.log N) /
        (H * Real.log N) ^ 2) := by field_simp
    _ = _ := by rw [fourth_formal_ratio H (Real.log N) E hH hL]

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
