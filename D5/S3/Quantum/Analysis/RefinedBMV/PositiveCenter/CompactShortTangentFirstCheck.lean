/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentFirstCheck
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact arithmetic for the first wide short-gap kernel sign. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentFirst

/-! Kernel-checked comparison on `1/2 ≤ u ≤ 1` and `0 < v-u ≤ 1/4`. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open private first_tangent_of_checks from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentFirst

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
/-- The midpoint tangent certifies the mixed derivative sign on the first wide short-gap box. -/
theorem logKernel_mixed_neg_short_tangent_first {p : ℕ} {u v : ℝ} (hp : 11 ≤ p)
    (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 1) (huv : u < v) (hd₁ : v - u ≤ 1 / 4) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  apply first_tangent_of_checks hp hu₀ hu₁ huv hd₁
  all_goals decide +kernel

end RefinedBMV.PositiveCenter.CompactTaylorModel
