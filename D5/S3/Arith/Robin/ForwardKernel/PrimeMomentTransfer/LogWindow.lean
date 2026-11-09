/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/LogWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dyadic logarithmic variance ratios and interval overlap pairings satisfy uniform bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FormalIntervalMomentBounds

/-! Logarithmic variance estimates on a dyadic window. -/

open Set

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

private theorem p_square_error_algebra (L A d c : ℝ) (hL : 0 < L) (hA : 0 ≤ A) (hAL : A ≤ L)
    (hd : 0 ≤ d) (hdc : d ≤ c) (hcL : c ≤ L) :
    |((A + d) / L) ^ 2 - (A / L) ^ 2| ≤ 3 * c / L := by
  have hc : 0 ≤ c := hd.trans hdc
  have had : A * d ≤ L * c := mul_le_mul hAL hdc hd hL.le
  have hdd : d * d ≤ c * L := mul_le_mul hdc (hdc.trans hcL) hd hc
  have heq : ((A + d) / L) ^ 2 - (A / L) ^ 2 = (2 * A * d + d ^ 2) / L ^ 2 := by
    field_simp
    ring
  rw [heq, abs_of_nonneg (by positivity)]
  apply (div_le_iff₀ (sq_pos_of_pos hL)).2
  have hcancel : (3 * c / L) * L ^ 2 = 3 * c * L := by field_simp
  rw [hcancel]
  nlinarith

theorem log_square_error (N H x : ℝ) (hN : 2 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N)
    (hx : x ∈ Icc N (2 * N)) :
    |((Real.log x - Real.log H) / Real.log N) ^ 2 - (kappa N H) ^ 2| ≤
      (3 * Real.log 2) / Real.log N := by
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := by linarith
  have hx0 : 0 < x := hN0.trans_le hx.1
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hLH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hHL : Real.log H ≤ Real.log N :=
    Real.strictMonoOn_log.monotoneOn hH0 hN0 hHN
  have hLx : Real.log N ≤ Real.log x :=
    Real.strictMonoOn_log.monotoneOn hN0 hx0 hx.1
  have hxL : Real.log x ≤ Real.log N + Real.log 2 := by
    calc
      _ ≤ Real.log (2 * N) := Real.strictMonoOn_log.monotoneOn hx0
        (show 0 < 2 * N by positivity) hx.2
      _ = _ := by rw [Real.log_mul (by norm_num) hN0.ne']; ring
  have hcL : Real.log 2 ≤ Real.log N :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hN0 hN
  have hs := p_square_error_algebra (Real.log N) (Real.log N - Real.log H)
    (Real.log x - Real.log N) (Real.log 2) hL (by linarith) (by linarith)
    (by linarith) (by linarith) hcL
  rw [show (Real.log N - Real.log H) + (Real.log x - Real.log N) =
    Real.log x - Real.log H by ring] at hs
  simpa only [kappa, Real.log_div hN0.ne' hH0.ne'] using hs

theorem variance_ratio_bounds (N H : ℝ) (hN : 2 ≤ N) (hH : 1 ≤ H)
    (hHN : H ≤ N) : 0 ≤ kappa N H ∧ kappa N H ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hLH : 0 ≤ Real.log H := Real.log_nonneg hH
  have hHL : Real.log H ≤ Real.log N :=
    Real.strictMonoOn_log.monotoneOn hH0 hN0 hHN
  rw [kappa, Real.log_div hN0.ne' hH0.ne']
  exact ⟨div_nonneg (sub_nonneg.mpr hHL) hL.le,
    (div_le_one hL).mpr (sub_le_self _ hLH)⟩

theorem w4_bound (M : ℝ) (a b : Fin 4 → ℝ) (hM : 0 ≤ M)
    (hab : admissible M a b) : 0 ≤ W4 a b ∧ W4 a b ≤ 3 * M ^ 2 := by
  have hs (i j : Fin 4) :
      0 ≤ sigma (a i) (b i) (a j) (b j) ∧ sigma (a i) (b i) (a j) (b j) ≤ M :=
    sigma_bound hM (hab i).1 (hab i).2.2 (hab j).1
  have hp (i j k l : Fin 4) :
      0 ≤ sigma (a i) (b i) (a j) (b j) * sigma (a k) (b k) (a l) (b l) ∧
      sigma (a i) (b i) (a j) (b j) * sigma (a k) (b k) (a l) (b l) ≤ M ^ 2 := by
    exact ⟨mul_nonneg (hs i j).1 (hs k l).1,
      (mul_le_mul (hs i j).2 (hs k l).2 (hs k l).1 hM).trans_eq (pow_two M).symm⟩
  obtain ⟨h₁, h₁'⟩ := hp 0 1 2 3
  obtain ⟨h₂, h₂'⟩ := hp 0 2 1 3
  obtain ⟨h₃, h₃'⟩ := hp 0 3 1 2
  unfold W4
  exact ⟨add_nonneg (add_nonneg h₁ h₂) h₃,
    (add_le_add (add_le_add h₁' h₂') h₃').trans_eq (by ring)⟩

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
