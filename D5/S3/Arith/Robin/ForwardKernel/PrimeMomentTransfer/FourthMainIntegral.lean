/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FourthMainIntegral
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FourthMainIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weighted fourth pairing integrals have an explicit inverse logarithmic error. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.LogWindow
import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.WeightedIntegralTools

/-! A uniform approximation for the integrated fourth pairing term. -/

open Set MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

theorem fourth_main_integral_error (N H M B : ℝ) (w : ℝ → ℝ) (a b : Fin 4 → ℝ)
    (hN : 2 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N) (hM : 0 ≤ M)
    (hw : BVBound w B) (hab : admissible M a b) :
    |(∫ x in N..2 * N, w (x / N) *
        (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) -
        N * (∫ t in (1 : ℝ)..2, w t) * (kappa N H) ^ 2 * W4 a b| ≤
      N * B * (9 * M ^ 2 * Real.log 2 / Real.log N) := by
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hB : 0 ≤ B := hw.2.2.1
  have hW := w4_bound M a b hM hab
  have hi := ((polynomial_weight_integrable N hN B w hw
    ((Polynomial.X - Polynomial.C (Real.log H)) ^ 2)).div_const
      ((Real.log N) ^ 2)).mul_const (W4 a b)
  have hi' : IntervalIntegrable (fun x => w (x / N) *
      (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) volume N (2 * N) := by
    convert hi using 1
    ext x
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    ring
  have hw' : IntervalIntegrable (fun x => w (x / N)) volume N (2 * N) := by
    simpa using polynomial_weight_integrable N hN B w hw (1 : Polynomial ℝ)
  have hc := (hw'.mul_const ((kappa N H) ^ 2)).mul_const (W4 a b)
  have heq : (∫ x in N..2 * N, w (x / N) *
        (((Real.log x - Real.log H) / Real.log N) ^ 2 * W4 a b)) -
        N * (∫ t in (1 : ℝ)..2, w t) * (kappa N H) ^ 2 * W4 a b =
      ∫ x in N..2 * N, w (x / N) *
        ((((Real.log x - Real.log H) / Real.log N) ^ 2 - (kappa N H) ^ 2) * W4 a b) := by
    have hscale := intervalIntegral.integral_comp_div w hN0.ne' (a := N) (b := 2 * N)
    simp only [div_self hN0.ne', mul_div_cancel_right₀ _ hN0.ne', smul_eq_mul] at hscale
    rw [← hscale, ← intervalIntegral.integral_mul_const,
      ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub hi' hc]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [heq]
  apply weighted_integral_uniform_bound N B _ w _ hN0.le hB (by positivity)
    (fun x _ => bv_sup_bound w B hw (x / N))
  intro x hx
  rw [abs_mul, abs_of_nonneg hW.1]
  calc
    _ ≤ (3 * Real.log 2 / Real.log N) * (3 * M ^ 2) :=
      mul_le_mul (log_square_error N H x hN hH hHN hx) hW.2 hW.1 (by positivity)
    _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
