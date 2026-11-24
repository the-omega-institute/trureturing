/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover/Replay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay and indexing for the short-gap quadrature cover. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureBox
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorReplay
import Lean.Elab.Tactic.Cbv

/-! Shared finite checks for the quadrature cover of the compact short-gap band. -/

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureCover

open CompactShortQuadratureBox (Checks Orders scoreModel)
open CompactTaylorModel.CompactShortBox (lowerCheck)
open CompactTaylorModel.ShortTangentGrid (Rectangle leaves)

open CompactTaylorModel (Model)
open CompactTaylorModel.Replay

open private CompactTaylorModel.Model.center from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary
open private coeffAdd coeffScale from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial

open private quadratureParameterRow quadratureShiftBound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortJointLower

scoped cbv_simproc cbv_eval stageParameterRow (quadratureParameterRow _ _ _ _) :=
  stageLiteral (List Rat)
scoped cbv_simproc cbv_eval stageShiftedRow (shiftedQuadratureParameterRow _ _ _ _ _ _) :=
  stageLiteral (List Rat)
scoped cbv_simproc cbv_eval stageShiftBound (quadratureShiftBound _ _ _ _ _ _) :=
  stageLiteral Rat
scoped cbv_simproc cbv_eval stageExpMoment (shortExpMomentBound _ _ _ _ _ _ _) :=
  stageLiteral Rat

scoped cbv_simproc cbv_eval stageMul (Model.mul _ _) := stageOnModels 2 stageModel
scoped cbv_simproc cbv_eval stageAdd (Model.add _ _) := stageOnModels 2 stageModel
scoped cbv_simproc cbv_eval stageSub (Model.sub _ _) := stageOnModels 2 stageModel
scoped cbv_simproc cbv_eval stageOfRat (Model.ofRat _) := stageModel
scoped cbv_simproc cbv_eval stageWiden (Model.widen _ _) := stageOnModels 1 stageModel
scoped cbv_simproc cbv_eval stageLower (Model.lower _) := stageOnModels 1 (stageLiteral Int)
scoped cbv_simproc cbv_eval stageAbsUpper (Model.absUpper _) := stageOnModels 1 (stageLiteral Nat)
scoped cbv_simproc cbv_eval stageCenter (CompactTaylorModel.Model.center _) :=
  stageOnModels 1 (stageLiteral Rat)
scoped cbv_simproc cbv_eval stageCoeffScale (coeffScale _ _) := stageLiteral (List Rat)
scoped cbv_simproc cbv_eval stageCoeffAdd (coeffAdd _ _) := stageLiteral (List Rat)

attribute [scoped cbv_opaque] Model.add Model.sub Model.mul Model.lower Model.absUpper

/-- Supply the finite side conditions and the score endpoint for a closed quadrature box.
Open the scope `CompactShortQuadratureCover` to activate its staged arithmetic replay. -/
scoped macro "replay_short_quadrature" : tactic =>
  `(tactic|
    refine And.intro (by
      constructor
      · intro i
        fin_cases i <;> decide_cbv
      · intro i j
        fin_cases i <;> fin_cases j <;> decide_cbv
      · intro i
        fin_cases i <;> decide_cbv
      · decide_cbv
      · decide_cbv
      · intro i
        fin_cases i <;> decide_cbv
      · decide_cbv
      · decide_cbv
      · constructor <;> decide_cbv
      · constructor <;> decide_cbv
      · decide_cbv) (by decide_cbv))

/-- The quadrature orders for the short-gap spacing subboxes. -/
def uniformOrders : Orders :=
  ⟨5, fun _ ↦ 36, fun _ ↦ ⟨fun _ ↦ 36, 29, 46⟩⟩

/-- The number of rectangles in the existing short-gap grid. -/
theorem leaves_length : leaves.length = 72 := by decide_cbv

/-- The rectangle at the given zero-based index in the existing short-gap grid. -/
def row (i : Fin 72) : Rectangle :=
  (leaves[i.val]'(by simpa only [leaves_length] using i.isLt)).box

/-- The finite side conditions and a degree-zero score check with positive endpoint one. -/
abbrev CheckedSubbox (box : Rectangle) (hLo hHi : ℚ) : Prop :=
  Checks box hLo hHi uniformOrders ∧
    lowerCheck (scoreModel box hLo hHi uniformOrders) 0 1 = true

end RefinedBMV.PositiveCenter.CompactShortQuadratureCover
