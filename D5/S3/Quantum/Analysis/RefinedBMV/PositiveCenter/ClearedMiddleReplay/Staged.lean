/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleReplay/Staged
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Stage the exact model arithmetic shared by the cleared middle-gap corner checks. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorReplay
import Lean.Elab.Tactic.Cbv

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid.Staged

open CompactTaylorModel.Replay
open private CompactMiddleBox.clearedScores CompactMiddleBox.elementaryChecks
  CompactMiddleBox.headChecks CompactMiddleBox.neg from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

scoped cbv_simproc cbv_eval stageMul (Model.mul _ _) := stageOnModels 2 stageModel
scoped cbv_simproc cbv_eval stageAdd (Model.add _ _) := stageOnModels 2 stageModel
scoped cbv_simproc cbv_eval stageSub (Model.sub _ _) := stageOnModels 2 stageModel
scoped cbv_simproc cbv_eval stageOfRat (Model.ofRat _) := stageModel
scoped cbv_simproc cbv_eval stageWiden (Model.widen _ _) := stageOnModels 1 stageModel
scoped cbv_simproc cbv_eval stageTruncate (Model.truncate _ _) := stageOnModels 1 stageModel
scoped cbv_simproc cbv_eval stageLower (Model.lower _) := stageOnModels 1 (stageLiteral Int)
scoped cbv_simproc cbv_eval stageHead (CompactMiddleBox.headChecks _ (Model.mk _ _)) :=
  stageLiteral Bool

attribute [scoped cbv_opaque] Model.mul Model.add Model.sub Model.ofRat Model.widen
  Model.truncate Model.lower CompactMiddleBox.headChecks

private def checkScores (degree : ℕ) (scores : Model × Model) : Bool :=
  decide (0 < (CompactMiddleBox.neg scores.1).lower) &&
    CompactMiddleBox.headChecks degree ((CompactMiddleBox.neg scores.2).truncate degree)

private def cornersCheck (leaf : Leaf) : Bool :=
  let box := leaf.model
  let d₀ := leaf.box.dLo
  let degree := leaf.degree
  let check := fun a b ↦ checkScores degree (CompactMiddleBox.clearedScores box d₀ a b)
  (check false false && check false true) && (check true false && check true true)

private theorem checked_of_corners (leaf : Leaf) (helem : leaf.model.ClearedChecks)
    (hdegree : leaf.degree ≤ 4) (hc : cornersCheck leaf = true) : leaf.Checked := by
  simp only [cornersCheck, Bool.and_eq_true] at hc
  have h (a b : Bool) :
      leaf.model.clearedZeroCheck leaf.box.dLo a b = true ∧
        leaf.model.clearedUpperCheck leaf.box.dLo a b leaf.degree = true := by
    have pair :
        checkScores leaf.degree (CompactMiddleBox.clearedScores leaf.model leaf.box.dLo a b) =
          true := by
      cases a
      · cases b
        · exact hc.1.1
        · exact hc.1.2
      · cases b
        · exact hc.2.1
        · exact hc.2.2
    unfold CompactMiddleBox.clearedZeroCheck CompactMiddleBox.clearedUpperCheck
    exact Bool.and_eq_true_iff.mp pair
  exact leaf.checked_of_tests helem hdegree (fun a b ↦ (h a b).1) (fun a b ↦ (h a b).2)

/-- Use one staged reduction so the closed model arithmetic is shared across the corners. -/
scoped macro "replay_staged_cleared_middle_leaf" : tactic => `(tactic| (
  apply checked_of_corners
  · constructor
    all_goals
      simp only [CompactMiddleBox.elementaryChecks, Model.expChecks]
      repeat' apply And.intro
      all_goals decide +kernel
  · decide +kernel
  · set_option cbv.maxSteps 5000000 in decide_cbv))

end RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid.Staged
