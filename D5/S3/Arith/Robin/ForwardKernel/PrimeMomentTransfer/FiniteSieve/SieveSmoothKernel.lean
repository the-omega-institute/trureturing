/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveSmoothKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A positive unit-mass smoothing kernel bounds the support of shifted interval averages. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveAnalyticDefs

/-! Positive shift averaging bounds the compact support of interval averages. -/

open Set MeasureTheory
open scoped Topology ContDiff Convolution

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

theorem smoothing_kernel_support (δ : ℝ) (hδ : 0 < δ) :
    tsupport (smoothingKernel δ hδ) = Icc δ (3 * δ) ∧
    Function.support (smoothingKernel δ hδ) = Ioo δ (3 * δ) := by
  constructor
  · rw [smoothingKernel, (sieveSmoothingBump δ hδ).tsupport_normed_eq, Real.closedBall_eq_Icc]
    congr 1 <;> simp only [sieveSmoothingBump] <;> ring
  · rw [smoothingKernel, (sieveSmoothingBump δ hδ).support_normed_eq, Real.ball_eq_Ioo]
    congr 1 <;> simp only [sieveSmoothingBump] <;> ring

theorem smoothing_kernel_mass (δ : ℝ) (hδ : 0 < δ) :
    (∀ r, 0 ≤ smoothingKernel δ hδ r) ∧ (∫ r, smoothingKernel δ hδ r) = 1 :=
  ⟨(sieveSmoothingBump δ hδ).nonneg_normed, (sieveSmoothingBump δ hδ).integral_normed⟩

theorem smooth_interval_support (δ : ℝ) (hδ : 0 < δ) (a b : ℝ)
    (_ha : 0 ≤ a) (_hab : a ≤ b) :
    HasCompactSupport (smoothedInterval δ hδ a b) ∧
      tsupport (smoothedInterval δ hδ a b) ⊆ Icc (a + δ) (b + 3 * δ) := by
  have hs : tsupport (smoothedInterval δ hδ a b) ⊆ Icc (a + δ) (b + 3 * δ) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hnot
    apply hx
    apply integral_eq_zero_of_ae
    filter_upwards [] with r
    by_cases hr : smoothingKernel δ hδ r = 0
    · simp [hr]
    · have hrmem : r ∈ Ioo δ (3 * δ) := by
        rw [← (smoothing_kernel_support δ hδ).2]
        exact hr
      have hxnot : x ∉ Ioc (a + r) (b + r) := by
        intro hxin
        apply hnot
        constructor <;> linarith [hxin.1, hxin.2, hrmem.1, hrmem.2]
      simp [hxnot]
  exact ⟨isCompact_Icc.of_isClosed_subset isClosed_closure hs, hs⟩


end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
