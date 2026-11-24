/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ClearedMiddleReplay/Pilot
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of the first complete cleared middle-gap leaf. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ClearedMiddleReplay.UpperHeadGapStage

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid

open private CompactMiddleBox.clearedScores CompactMiddleBox.elementaryChecks
  CompactMiddleBox.headChecks CompactMiddleBox.neg CompactMiddleBox.upperRadicand
  CompactMiddleBox.weights from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

section

attribute [local cbv_simproc cbv_eval] stageMul stageAdd stageSub stageOfRat stageWiden
attribute [local cbv_opaque] Model.mul Model.add Model.sub Model.ofRat Model.widen

private def firstScores (a b : Bool) : Model × Model :=
  let leaf := leafAt 0
  CompactMiddleBox.clearedScores leaf.model leaf.box.dLo a b

private def checkZeroScore (score : Model) : Bool :=
  decide (0 < (CompactMiddleBox.neg score).lower)

private def checkUpperScore (score : Model) : Bool :=
  let degree := (leafAt 0).degree
  CompactMiddleBox.headChecks degree ((CompactMiddleBox.neg score).truncate degree)

private def firstEndpointChecks (scores : Model × Model) : Bool :=
  checkZeroScore scores.1 && checkUpperScore scores.2

-- Keep the endpoint and score lets for the paired replay.
local macro "replay_first_corner" : tactic => `(tactic| (
  conv_lhs =>
    arg 1
    simp only [firstScores, CompactMiddleBox.clearedScores, CompactMiddleBox.weights,
      CompactMiddleBox.upperRadicand, first_upper_gap_fv_eq]
    cbv
  all_goals decide +kernel))

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
-- Normalize only the score needed for this endpoint.
private theorem first_zero_false_false : checkZeroScore (firstScores false false).1 = true := by
  conv_lhs =>
    arg 1
    -- Reduce the projections before cbv evaluates the models behind them.
    dsimp only [firstScores, CompactMiddleBox.clearedScores, middleClearedEndpointModels,
      middleScoreCoreModels, middleDefectModels, middleClearedJetModels, CompactMiddleBox.weights,
      middleWeightModels]
    simp only [first_upper_gap_fv_eq]
    cbv
  all_goals decide +kernel

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
-- Share the model inputs of this corner's two scores.
private theorem first_false_true : firstEndpointChecks (firstScores false true) = true := by
  replay_first_corner

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
-- Share the model inputs of this corner's two scores.
private theorem first_true_false : firstEndpointChecks (firstScores true false) = true := by
  replay_first_corner

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
-- Share the model inputs of this corner's two scores.
private theorem first_true_true : firstEndpointChecks (firstScores true true) = true := by
  replay_first_corner

end

private theorem first_corners_checked (a b : Bool) :
    (leafAt 0).model.clearedZeroCheck (leafAt 0).box.dLo a b = true ∧
      (leafAt 0).model.clearedUpperCheck (leafAt 0).box.dLo a b (leafAt 0).degree = true := by
  cases a
  · cases b
    · exact ⟨first_zero_false_false, firstUpperCorner_checked⟩
    · exact Bool.and_eq_true.mp first_false_true
  · cases b
    · exact Bool.and_eq_true.mp first_true_false
    · exact Bool.and_eq_true.mp first_true_true

private theorem first_elementary_checked : (leafAt 0).model.ClearedChecks := by
  constructor
  all_goals
    simp only [CompactMiddleBox.elementaryChecks, Model.expChecks]
    repeat' apply And.intro
    all_goals decide +kernel

/-- All elementary checks and all four corners for `[1/2, 5/8] × [1, 5/4]`. -/
theorem pilot_checked : (leafAt 0).Checked := by
  apply Leaf.checked_of_tests
  · exact first_elementary_checked
  · decide +kernel
  · exact fun a b ↦ (first_corners_checked a b).1
  · exact fun a b ↦ (first_corners_checked a b).2

#print axioms pilot_checked

end RefinedBMV.PositiveCenter.CompactTaylorModel.ClearedMiddleGrid
