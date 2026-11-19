/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded variation weights supply supremum and weighted integral bounds. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.WeightedArithmeticTransfer

/-! Integration tools for supported bounded variation weights. -/

open Set MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

theorem bv_sup_bound (w : ℝ → ℝ) (B : ℝ) (hw : BVBound w B) (t : ℝ) :
    |w t| ≤ B := by
  obtain ⟨U, _, hU, hUB⟩ := hw.2.2.2
  exact (hU t).trans ((le_add_of_nonneg_right ENNReal.toReal_nonneg).trans hUB)

theorem weighted_integral_uniform_bound (N B E : ℝ) (w f : ℝ → ℝ)
    (hN : 0 ≤ N) (_hB : 0 ≤ B) (_hE : 0 ≤ E)
    (hw : ∀ x ∈ Icc N (2 * N), |w (x / N)| ≤ B)
    (hf : ∀ x ∈ Icc N (2 * N), |f x| ≤ E) :
    |∫ x in N..2 * N, w (x / N) * f x| ≤ N * B * E := by
  have hNN : N ≤ 2 * N := by linarith
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := N) (b := 2 * N) (C := B * E) (f := fun x => w (x / N) * f x)
    (fun x hx => by
      have hx' : x ∈ Icc N (2 * N) :=
        ⟨(show x ∈ Ioc N (2 * N) from (uIoc_of_le hNN) ▸ hx).1.le,
          (show x ∈ Ioc N (2 * N) from (uIoc_of_le hNN) ▸ hx).2⟩
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hw x hx') (hf x hx') (abs_nonneg _) _hB)
  rw [Real.norm_eq_abs, show 2 * N - N = N by ring, abs_of_nonneg hN] at hb
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hb


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
