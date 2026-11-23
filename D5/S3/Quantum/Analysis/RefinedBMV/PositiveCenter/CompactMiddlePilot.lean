/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMiddlePilot
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The compact middle-gap kernel sign on a single unsplit grid cell. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open private CompactMiddleBox.elementaryChecks from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

private def pilotBox : CompactMiddleBox :=
  CompactMiddleBox.ofIntervals 2 3 (5 / 4) (3 / 2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem pilotElementaries : pilotBox.Checks := by
  constructor
  case checkUpperGapProduct =>
    intro product h
    cases h
  all_goals
    simp only [CompactMiddleBox.elementaryChecks, Model.expChecks]
    repeat' apply And.intro
    all_goals decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem pilotCorners (a b : Bool) : pilotBox.EndpointTests a b := by
  cases a <;> cases b <;> apply pilotBox.endpointTests_of_direct_checks
  all_goals decide +kernel

/-- The original mixed derivative is negative on the unsplit middle cell
`2 ≤ u ≤ 3`, `5/4 ≤ v - u ≤ 3/2`, uniformly in `p ≥ 11`. -/
theorem logKernel_mixed_neg_middle_pilot {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₀ : 2 ≤ u) (hu₁ : u ≤ 3) (hd₀ : 5 / 4 ≤ v - u) (hd₁ : v - u ≤ 3 / 2) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨s, t, z, hb, hU, hD, hH⟩ :=
    CompactMiddleBox.boxCoordinates hp (u₀ := 2) (u₁ := 3) (d₀ := 5 / 4) (d₁ := 3 / 2)
      (by norm_num) (by norm_num) (by norm_num; exact hu₀) (by norm_num; exact hu₁)
      (by norm_num; exact hd₀) (by norm_num; exact hd₁)
  exact pilotBox.mixed_neg_of_checks hp (by linarith) (by linarith) (by linarith)
    hb hU hD hH pilotElementaries pilotCorners

end RefinedBMV.PositiveCenter.CompactTaylorModel
