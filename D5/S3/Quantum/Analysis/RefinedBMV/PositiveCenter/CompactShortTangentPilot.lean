/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortTangentPilot
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay of the first normalized short-gap table row. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortTangentData
import Lean.Elab.Tactic.Cbv
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorReplay

/-! The first checked row of the normalized short-gap table. -/

namespace RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay

open Lean Meta Sym.Simp
open DimThree.Certificate (Sparse Term)

open private CompactShortBox.U CompactShortBox.V CompactShortBox.ZV CompactShortBox.ZD
  CompactShortBox.marginal CompactShortBox.neg CompactShortBox.multiplier CompactShortBox.negScore
  CompactShortBox.expUpper from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortBox
open private Model.center from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary
open private shortMomentTaylorCoefficientsFromTable from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortMomentEnclosure
open private coeffAdd coeffScale from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial

section

open CompactTaylorModel.Replay

-- These simprocs receive the arguments after cbv has reduced them.
local cbv_simproc cbv_eval stageMul (Model.mul _ _) := stageOnModels 2 stageModel
local cbv_simproc cbv_eval stageAdd (Model.add _ _) := stageOnModels 2 stageModel
local cbv_simproc cbv_eval stageSub (Model.sub _ _) := stageOnModels 2 stageModel
local cbv_simproc cbv_eval stageOfRat (Model.ofRat _) := stageModel
local cbv_simproc cbv_eval stageWiden (Model.widen _ _) :=
  stageOnModels 1 stageModel
local cbv_simproc cbv_eval stageLower (Model.lower _) :=
  stageOnModels 1 (stageLiteral Int)
local cbv_simproc cbv_eval stageAbsUpper (Model.absUpper _) :=
  stageOnModels 1 (stageLiteral Nat)
local cbv_simproc cbv_eval stageCenter (Model.center _) :=
  stageOnModels 1 (stageLiteral Rat)
local cbv_simproc cbv_eval stageExpUpper (CompactShortBox.expUpper _ _) := stageLiteral Rat
local cbv_simproc cbv_eval stageMarginalCoefficients
    (CompactShortMomentTable.marginalCoefficients _) := stageLiteral (List Rat)
local cbv_simproc cbv_eval stageMidpointCoefficients
    (shortMomentTaylorCoefficientsFromTable _ _ _) := stageLiteral (List Rat)
-- Collect each scaled Taylor list with a single kernel-checked equality per operation.
local cbv_simproc cbv_eval stageCoeffScale (coeffScale _ _) := stageLiteral (List Rat)
local cbv_simproc cbv_eval stageCoeffAdd (coeffAdd _ _) := stageLiteral (List Rat)
local cbv_simproc cbv_eval stageShortSpacing (Model.shortSpacing _) := stageModel
local cbv_simproc cbv_eval stageLowerCheck (CompactShortBox.lowerCheck _ _ _) :=
  stageOnModels 1 (stageLiteral Bool)

attribute [local cbv_opaque] Model.add Model.sub Model.mul Model.lower Model.absUpper
attribute [local cbv_opaque] Model.shortSpacing

private def pilotBox : CompactShortBox := ⟨63 / 16, 4, 7 / 8, 1, 457 / 64, 27, 30, 6⟩

private def arithmeticChecks : Bool :=
  let u := CompactShortBox.U pilotBox
  let v := CompactShortBox.V pilotBox
  let reflected := fun x => CompactShortBox.marginal pilotBox 0 (CompactShortBox.neg x)
  let lowerCheck := CompactShortBox.lowerCheck
  decide (0 < u.lower) &&
  (decide (0 < v.lower) &&
  (decide (0 < (CompactShortBox.ZV pilotBox).lower) &&
  (decide (0 < (CompactShortBox.ZD pilotBox).lower) &&
  (decide (0 < (reflected u).lower) &&
  (decide (0 < (reflected v).lower) &&
  (lowerCheck (CompactShortBox.multiplier pilotBox) 0 0 &&
    lowerCheck (CompactShortBox.negScore pilotBox) 0 1))))))

set_option maxRecDepth 20000 in
set_option cbv.maxSteps 5000000 in
set_option maxHeartbeats 0 in
-- One replay shares the reduced models across the eight arithmetic fields.
private theorem arithmeticChecks_true : arithmeticChecks = true := by
  decide_cbv

/-- Row 1 of `central-short-compact-normalized-20261124.jsonl`. -/
def pilot : CheckedBox := ⟨pilotBox, by
  have h := arithmeticChecks_true
  simp only [arithmeticChecks, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hu, hv, hzv, hzd, hzuNeg, hzvNeg, hmultiplier, hscore⟩ := h
  refine {
    uMin := ?_, uMax := ?_, uWidth := ?_, dMin := ?_, dMax := ?_, dWidth := ?_
    rootPos := ?_, marginalOrder := ?_, centerOrder := ?_, offsetOrder := ?_
    marginalRatio := ?_, centerRatio := ?_, offsetRatio := ?_, endpointPos := ?_
    uPos := hu, vPos := hv, zvPos := hzv, zdPos := hzd, zuNegPos := hzuNeg, zvNegPos := hzvNeg
    multiplierLower := hmultiplier, scoreLower := hscore }
  all_goals decide +kernel⟩

end

end RefinedBMV.PositiveCenter.CompactTaylorModel.ShortTangentReplay
