/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureHighSpacing
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Short-gap quadrature sign on the high-spacing half of the first rectangle. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureBox
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortQuadratureFirstBox
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorReplay
import Lean.Elab.Tactic.Cbv

namespace RefinedBMV.PositiveCenter.CompactShortQuadratureHighSpacing

open CompactShortQuadratureBox (Checks Orders scoreModel score_pos_of_checks)
open CompactTaylorModel.CompactShortBox (lowerCheck)
open CompactTaylorModel.ShortTangentGrid (Rectangle)

private def box : Rectangle := ⟨63 / 16, 4, 7 / 8, 1⟩

private def orders : Orders where
  localOrder := 5
  jointTerms := fun _ ↦ 36
  marginals := ![⟨fun _ ↦ 36, 29, 46⟩, ⟨fun _ ↦ 36, 29, 46⟩,
    ⟨fun _ ↦ 36, 29, 46⟩, ⟨fun _ ↦ 36, 29, 46⟩]

section

open CompactTaylorModel (Model)
open CompactTaylorModel.Replay

open private CompactTaylorModel.Model.center from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactTaylorElementary
open private coeffAdd coeffScale from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial

open private quadratureParameterRow quadratureShiftBound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactShortJointLower

local cbv_simproc cbv_eval stageParameterRow (quadratureParameterRow _ _ _ _) :=
  stageLiteral (List Rat)
local cbv_simproc cbv_eval stageShiftedRow (shiftedQuadratureParameterRow _ _ _ _ _ _) :=
  stageLiteral (List Rat)
local cbv_simproc cbv_eval stageShiftBound (quadratureShiftBound _ _ _ _ _ _) :=
  stageLiteral Rat
local cbv_simproc cbv_eval stageExpMoment (shortExpMomentBound _ _ _ _ _ _ _) :=
  stageLiteral Rat

local cbv_simproc cbv_eval stageMul (Model.mul _ _) := stageOnModels 2 stageModel
local cbv_simproc cbv_eval stageAdd (Model.add _ _) := stageOnModels 2 stageModel
local cbv_simproc cbv_eval stageSub (Model.sub _ _) := stageOnModels 2 stageModel
local cbv_simproc cbv_eval stageOfRat (Model.ofRat _) := stageModel
local cbv_simproc cbv_eval stageWiden (Model.widen _ _) := stageOnModels 1 stageModel
local cbv_simproc cbv_eval stageLower (Model.lower _) := stageOnModels 1 (stageLiteral Int)
local cbv_simproc cbv_eval stageAbsUpper (Model.absUpper _) := stageOnModels 1 (stageLiteral Nat)
local cbv_simproc cbv_eval stageCenter (CompactTaylorModel.Model.center _) :=
  stageOnModels 1 (stageLiteral Rat)
local cbv_simproc cbv_eval stageCoeffScale (coeffScale _ _) := stageLiteral (List Rat)
local cbv_simproc cbv_eval stageCoeffAdd (coeffAdd _ _) := stageLiteral (List Rat)

attribute [local cbv_opaque] Model.add Model.sub Model.mul Model.lower Model.absUpper

set_option maxRecDepth 20000
set_option cbv.maxSteps 5000000
set_option maxHeartbeats 0

private theorem checks : Checks box (3 / 22) (3 / 11) orders := by
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
  · decide_cbv

private theorem scoreLower :
    lowerCheck (scoreModel box (3 / 22) (3 / 11) orders) 0 1 = true := by
  decide_cbv

end

/-- The exact scaled negative score is positive on the first rectangle when
the lattice spacing is between `3 / 22` and `3 / 11`. -/
theorem score_pos {p : ℕ} {u v : ℝ} (hpLo : 11 ≤ p) (hpHi : p ≤ 22)
    (huLo : 63 / 16 ≤ u) (huHi : u ≤ 4) (hdLo : 7 / 8 ≤ v - u) (hdHi : v - u ≤ 1) :
    0 < shortQuadratureNegativeScore p u v := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpLo' : (11 : ℝ) ≤ p := by exact_mod_cast hpLo
  have hpHi' : (p : ℝ) ≤ 22 := by exact_mod_cast hpHi
  have hpoint : box.Contains u (v - u) := by
    simpa only [Rectangle.Contains, box, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
      And.intro huLo (And.intro huHi (And.intro hdLo hdHi))
  refine score_pos_of_checks checks scoreLower (by norm_num) hpLo ?_ hpoint (by norm_num) ?_ ?_
  · change (1 / 2 ≤ (63 / 16 : ℚ) ∧ 63 / 16 < 4 ∧ 4 ≤ 4) ∧
      (0 ≤ (7 / 8 : ℚ) ∧ 7 / 8 < 1 ∧ 1 ≤ 1)
    norm_num
  · push_cast
    exact div_le_div_of_nonneg_left (by norm_num) hpPos hpHi'
  · push_cast
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpLo'

/-- The mixed logarithmic derivative is strictly negative on the high-spacing
half of the first short-gap rectangle. -/
theorem logKernel_mixed_lt {p : ℕ} {u v : ℝ} (hpLo : 11 ≤ p) (hpHi : p ≤ 22)
    (huLo : 63 / 16 ≤ u) (huHi : u ≤ 4) (hdLo : 7 / 8 ≤ v - u) (hdHi : v - u ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 :=
  logKernel_mixed_neg_of_shortQuadratureNegativeScore hpLo (by linarith) (by linarith) hdHi
    (score_pos hpLo hpHi huLo huHi hdLo hdHi)

end RefinedBMV.PositiveCenter.CompactShortQuadratureHighSpacing

namespace RefinedBMV.PositiveCenter

/-- The first short-gap rectangle satisfies the mixed sign for every degree at least eleven. -/
theorem logKernel_mixed_lt_firstShortRectangle {p : ℕ} {u v : ℝ} (hp : 11 ≤ p)
    (huLo : 63 / 16 ≤ u) (huHi : u ≤ 4) (hdLo : 7 / 8 ≤ v - u) (hdHi : v - u ≤ 1) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  by_cases h : p ≤ 22
  · exact CompactShortQuadratureHighSpacing.logKernel_mixed_lt hp h huLo huHi hdLo hdHi
  · exact CompactShortQuadratureFirstBox.logKernel_mixed_lt (by omega) huLo huHi hdLo hdHi

end RefinedBMV.PositiveCenter
