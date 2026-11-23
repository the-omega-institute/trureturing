/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMiddleFirstBand
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Model enclosures for the first box of the compact middle-gap kernel. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

/-! The compact box with `3/4 ≤ u ≤ 7/8` and `1 ≤ v - u ≤ 17/16`. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open private rate from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactGapIdentities

open private CompactMiddleBox.elementaryChecks from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

private def firstBox : CompactMiddleBox :=
  CompactMiddleBox.ofIntervals (3 / 4) (7 / 8) 1 (17 / 16)

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem firstElementaries : firstBox.Checks := by
  constructor
  case checkUpperGapProduct =>
    intro product h
    cases h
  all_goals
    simp only [CompactMiddleBox.elementaryChecks, Model.expChecks]
    repeat' apply And.intro
    all_goals decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem firstZeroCheck : firstBox.zeroCheck false false = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem firstUpperCheck : firstBox.upperDirectCheck false false = true := by
  decide +kernel

private theorem firstLowerSlopes : firstBox.EndpointTests false false :=
  firstBox.endpointTests_of_direct_checks false false firstZeroCheck firstUpperCheck

/-- The first middle-gap box reduces to its four endpoint tests. -/
theorem logKernel_mixed_neg_middle_first_of_tests {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₁ : 3 / 4 ≤ u) (hu₂ : u ≤ 7 / 8) (hd₁ : 1 ≤ v - u) (hd₂ : v - u ≤ 17 / 16)
    (hcorner : ∀ a b : Bool, firstBox.EndpointTests a b) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨s, t, z, hb, hU, hD, hH⟩ :=
    CompactMiddleBox.boxCoordinates hp (u₀ := 3 / 4) (u₁ := 7 / 8) (d₀ := 1) (d₁ := 17 / 16)
      (by norm_num) (by norm_num) (by norm_num; exact hu₁) (by norm_num; exact hu₂)
      (by norm_num; linarith) (by norm_num; linarith)
  exact firstBox.mixed_neg_of_checks hp (by linarith) (by linarith) hd₁ hb hU hD hH
    firstElementaries hcorner

end RefinedBMV.PositiveCenter.CompactTaylorModel
