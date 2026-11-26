/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleReplay/Split
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cover the wider cleared middle-gap leaf by two checked rectangles. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Staged

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid

open scoped Staged

private def leftLeaf : Leaf := ⟨⟨1, 3 / 2, 5 / 2, 3⟩, 2⟩
private def rightLeaf : Leaf := ⟨⟨3 / 2, 2, 5 / 2, 3⟩, 2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem left_checked : leftLeaf.Checked := by
  replay_staged_cleared_middle_leaf

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem right_checked : rightLeaf.Checked := by
  replay_staged_cleared_middle_leaf

/-- The leaf with index 22 uses two degree-two tests after bisection in `u`. -/
theorem split_mixedNegative : (leafAt 22).box.MixedNegative := by
  change (⟨1, 2, 5 / 2, 3⟩ : Rectangle).MixedNegative
  intro p u v hp hmem
  obtain ⟨huLo, huHi, hdLo, hdHi⟩ := hmem
  by_cases hmid : u ≤ 3 / 2
  · have hvalid : leftLeaf.box.Valid := by norm_num [leftLeaf, Rectangle.Valid]
    have hhi : u ≤ (leftLeaf.box.uHi : ℝ) := by
      simpa only [leftLeaf, Rat.cast_div, Rat.cast_ofNat] using hmid
    exact Leaf.mixedNegative_of_checked hvalid left_checked hp ⟨huLo, hhi, hdLo, hdHi⟩
  · have hvalid : rightLeaf.box.Valid := by norm_num [rightLeaf, Rectangle.Valid]
    have hlo : (rightLeaf.box.uLo : ℝ) ≤ u := by
      simpa only [rightLeaf, Rat.cast_div, Rat.cast_ofNat] using (le_of_not_ge hmid)
    exact Leaf.mixedNegative_of_checked hvalid right_checked hp ⟨hlo, huHi, hdLo, hdHi⟩

end RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid
