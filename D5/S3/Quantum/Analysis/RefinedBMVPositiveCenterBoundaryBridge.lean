/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterBoundaryBridge
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVPositiveCenterBoundaryBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Passage from the log-kernel mixed sign to arbitrary finite PSD matrices. -/

import D5.S3.Quantum.Analysis.RefinedBMVExtremeAnalytic
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterLeftLimit
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterRightLimit

/-! # Reduction of the all-degree bound to the mixed derivative sign -/

open Filter
open scoped Topology

noncomputable section

namespace RefinedBMV.PositiveCenter

universe u

/-- Only the mixed-derivative sign remains after the two endpoint limits.
The result includes the zero center and arbitrarily large finite samples. -/
theorem upperPSD_of_logKernel_mixed {p : ℕ} (hp : 0 < p)
    (hmixed : ∀ u v : ℝ, 0 < u → u < v →
      deriv (fun t ↦ deriv (fun s ↦ logKernel p s t) u) v ≤ 0) :
    ExtremeWalk.UpperPSD.{u} p := by
  refine Extreme.upperPSD_of_positive_center_mixed hp ?_ ?_ ?_
  · intro a ha u v hu huv
    simpa only [Extreme.logKernelAt_eq_logKernel hp ha] using hmixed u v hu huv
  · intro a ha v hv
    simpa only [Extreme.logKernelAt_eq_logKernel hp ha] using tendsto_logKernel_left hp hv
  · intro a ha u hu
    let x := a * Real.exp (u / (p : ℝ))
    have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    have hx : a < x := by
      have he : 1 < Real.exp (u / (p : ℝ)) := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (div_pos hu hp')
      simpa only [x, mul_one] using mul_lt_mul_of_pos_left he ha
    have ht : Tendsto (fun v : ℝ ↦ a * Real.exp (v / (p : ℝ))) atTop atTop := by
      have hd : Tendsto (fun v : ℝ ↦ v / (p : ℝ)) atTop atTop :=
        tendsto_id.atTop_div_const hp'
      exact (Real.tendsto_exp_atTop.comp hd).const_mul_atTop ha
    have h := (kernel_tendsto_right hp ha hx).comp ht
    exact h

#print axioms upperPSD_of_logKernel_mixed

end RefinedBMV.PositiveCenter
