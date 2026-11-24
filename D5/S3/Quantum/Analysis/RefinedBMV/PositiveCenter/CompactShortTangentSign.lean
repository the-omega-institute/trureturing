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

private def boxKey (box : CompactShortBox) : ShortTangentGrid.Rectangle × ℚ :=
  (⟨box.uLo, box.uHi, box.dLo, box.dHi⟩, box.root)

private def leafKey (leaf : ShortTangentGrid.Leaf) : ShortTangentGrid.Rectangle × ℚ :=
  (leaf.box, leaf.root)

private def checkedBoxes : List CheckedBox :=
  [pilot] ++ rows02To09 ++ rows10To17 ++ rows18To25 ++ rows26To33 ++
    rows34To41 ++ rows42To49 ++ rows50To57 ++
    rows58To65 ++ rows66To72

deriving instance DecidableEq for ShortTangentGrid.Rectangle

-- Match every checked row to the exact endpoints and tangent root of its grid leaf.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem grid_keys_eq :
    ShortTangentGrid.leaves.map leafKey = checkedBoxes.map (fun checked ↦ boxKey checked.val) := by
  decide +kernel

/-- The original mixed derivative is strictly negative for every degree at least eleven
throughout `1/2 ≤ u ≤ 4` and `0 < v - u ≤ 1`. -/
theorem logKernel_mixed_neg_short_tangent {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (huLo : 1 / 2 ≤ u) (huHi : u ≤ 4) (huv : u < v) (hdHi : v - u ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨leaf, hleaf, hcontains, _⟩ :=
    ShortTangentGrid.exists_leaf huLo huHi (sub_pos.mpr huv).le hdHi
  have hmem : leafKey leaf ∈ checkedBoxes.map (fun checked ↦ boxKey checked.val) := by
    rw [← grid_keys_eq]
    exact List.mem_map_of_mem hleaf
  obtain ⟨checked, _, heq⟩ := List.mem_map.mp hmem
  have hrect : (boxKey checked.val).1 = leaf.box := congrArg Prod.fst heq
  have hb : (boxKey checked.val).1.Contains u (v - u) := hrect.symm ▸ hcontains
  exact CompactShortBox.mixed_neg_of_checks checked.val hp checked.property
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 huv

end RefinedBMV.PositiveCenter.CompactTaylorModel
