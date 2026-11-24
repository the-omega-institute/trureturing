/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform strict mixed derivative sign on the compact short-gap band. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentGrid
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentPilot
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows02To09
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows10To17
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows18To25
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows26To33
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows34To41
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows42To49
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows50To57
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows58To65
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentRows66To72

/-! The original kernel has negative mixed derivative on the entire compact short-gap band. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open ShortTangentReplay

private def boxOfLeaf (leaf : ShortTangentGrid.Leaf) : CompactShortBox :=
  mkBox leaf.box.uLo leaf.box.uHi leaf.box.dLo leaf.box.dHi leaf.root

private def checkedBoxes : List CheckedBox :=
  [pilot] ++ rows02To09 ++ rows10To17 ++ rows18To25 ++ rows26To33 ++
    rows34To41 ++ rows42To49 ++ rows50To57 ++
    rows58To65 ++ rows66To72

deriving instance DecidableEq for CompactShortBox

-- Match every checked row to the exact endpoints and tangent root of its grid leaf.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem grid_boxes_eq :
    ShortTangentGrid.leaves.map boxOfLeaf = checkedBoxes.map Subtype.val := by
  decide +kernel

/-- The original mixed derivative is strictly negative for every degree at least eleven
throughout `1/2 ≤ u ≤ 4` and `0 < v - u ≤ 1`. -/
theorem logKernel_mixed_neg_short_tangent {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (huLo : 1 / 2 ≤ u) (huHi : u ≤ 4) (huv : u < v) (hdHi : v - u ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨leaf, hleaf, hcontains, _⟩ :=
    ShortTangentGrid.exists_leaf huLo huHi (sub_pos.mpr huv).le hdHi
  have hmem : boxOfLeaf leaf ∈ checkedBoxes.map Subtype.val := by
    rw [← grid_boxes_eq]
    exact List.mem_map_of_mem hleaf
  obtain ⟨checked, _, heq⟩ := List.mem_map.mp hmem
  have hchecks : (boxOfLeaf leaf).Checks 0 1 := heq ▸ checked.property
  exact CompactShortBox.mixed_neg_of_checks (boxOfLeaf leaf) hp hchecks
    hcontains.1 hcontains.2.1 hcontains.2.2.1 hcontains.2.2.2 huv

end RefinedBMV.PositiveCenter.CompactTaylorModel
