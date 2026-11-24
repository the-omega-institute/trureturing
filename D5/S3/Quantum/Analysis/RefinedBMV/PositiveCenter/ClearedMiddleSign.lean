/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleSign
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original kernel has a strictly negative mixed derivative on the full central middle band. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Pilot
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Batch1
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Batch2
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Batch3
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Batch4
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Batch5
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.Split
import Mathlib.Data.List.Basic

namespace RefinedBMV.PositiveCenter.CompactTaylorModel

open ClearedMiddleGrid

private theorem leafAt_mixedNegative (i : Fin 39) : (leafAt i).box.MixedNegative := by
  intro p u v hp hmem
  have hi := i.isLt
  by_cases hpilot : i.val = 0
  · have heq : i = 0 := Fin.ext hpilot
    subst i
    exact Leaf.mixedNegative_of_checked (valid_of_mem_leaves (leafAt_mem 0)) pilot_checked hp hmem
  by_cases h₁ : i.val < 8
  · exact mixedNegative_of_batch (h := by decide) batch1_checked
      (i := i) (by omega) (by omega) hp hmem
  by_cases h₂ : i.val < 14
  · exact mixedNegative_of_batch (h := by decide) batch2_checked
      (i := i) (by omega) (by omega) hp hmem
  by_cases h₃ : i.val < 22
  · exact mixedNegative_of_batch (h := by decide) batch3_checked
      (i := i) (by omega) (by omega) hp hmem
  by_cases hsplit : i.val = 22
  · have heq : i = 22 := Fin.ext hsplit
    subst i
    exact split_mixedNegative hp hmem
  by_cases h₄ : i.val < 32
  · exact mixedNegative_of_batch (h := by decide) batch4_checked
      (i := i) (by omega) (by omega) hp hmem
  exact mixedNegative_of_batch (h := by decide) batch5_checked
    (i := i) (by omega) (by omega) hp hmem

/-- The original mixed derivative is strictly negative on the whole central middle band,
including the boundaries `v - u = 1` and `v - u = 4`. -/
theorem logKernel_mixed_neg_cleared_middle {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (huLo : 1 / 2 ≤ u) (huHi : u ≤ 4) (hdLo : 1 ≤ v - u) (hdHi : v - u ≤ 4) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  obtain ⟨j, hmem⟩ := List.exists_mem_iff_get.mp (exists_leaf huLo huHi hdLo hdHi)
  exact leafAt_mixedNegative (j.cast leaves_length) hp hmem

end RefinedBMV.PositiveCenter.CompactTaylorModel
