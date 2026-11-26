/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactShortQuadratureCover/Replay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel replay and indexing for the short-gap quadrature cover. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortQuadrature.CompactShortQuadratureBox
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
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortQuadrature.CompactShortJointLower

open private coeffSum from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MomentPolynomial
open private marginalDensity marginalWeight marginalQuadratureTailBound jointDensityTailBound from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortQuadrature.CompactShortJointLower

private def rawPrefix (f : ℕ → List ℚ) : List (List ℚ) :=
  (List.range 36).map f

-- Quotation supplies data for the equalities below. Each equality is checked by the kernel.
local elab "quoteQuadraturePrefix% " t:term : term => do
  let type := Lean.toTypeExpr (α := List (List Rat))
  let e ← Lean.Elab.Term.elabTermEnsuringType t type
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let value ← unsafe Lean.Meta.evalExpr (List (List Rat)) type (← Lean.instantiateMVars e)
  return Lean.toExpr value

private def prefixRow (cs : List (List ℚ)) (f : ℕ → List ℚ) (n : ℕ) : List ℚ :=
  match cs[n]? with
  | some row => row
  | none => f n

private theorem prefixRow_rawPrefix (f : ℕ → List ℚ) (n : ℕ) :
    prefixRow (rawPrefix f) f n = f n := by
  unfold prefixRow rawPrefix
  rw [List.getElem?_map]
  by_cases h : n < 36
  · simp only [List.getElem?_range h, Option.map_some]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt h)]
    rfl

private def jointFormula (i : Fin 3) : ℕ → List ℚ :=
  quadratureParameterRow (shortJointDensityRow i) 0 (fun _ ↦ 1)

private def marginalFormula (j : ℕ) : ℕ → List ℚ :=
  quadratureParameterRow marginalDensity (j + 2) (marginalWeight j)

private def jointPrefix : Fin 3 → List (List ℚ)
  | 0 => quoteQuadraturePrefix% rawPrefix (jointFormula 0)
  | 1 => quoteQuadraturePrefix% rawPrefix (jointFormula 1)
  | 2 => quoteQuadraturePrefix% rawPrefix (jointFormula 2)

private def marginalPrefix : ℕ → List (List ℚ)
  | 0 => quoteQuadraturePrefix% rawPrefix (marginalFormula 0)
  | 1 => quoteQuadraturePrefix% rawPrefix (marginalFormula 1)
  | 2 => quoteQuadraturePrefix% rawPrefix (marginalFormula 2)
  | _ + 3 => []

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem jointPrefix_eq (i : Fin 3) : jointPrefix i = rawPrefix (jointFormula i) := by
  fin_cases i <;> decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem marginalPrefix_eq : ∀ i : Fin 3, marginalPrefix i.val = rawPrefix (marginalFormula i.val) := by
  intro i
  fin_cases i <;> decide +kernel

private def jointRows (i : Fin 3) (n : ℕ) : List ℚ :=
  prefixRow (jointPrefix i) (jointFormula i) n

private def marginalRows (j n : ℕ) : List ℚ :=
  prefixRow (marginalPrefix j) (marginalFormula j) n

private theorem jointRows_eq (i : Fin 3) : jointRows i = jointFormula i := by
  funext n
  rw [jointRows, jointPrefix_eq, prefixRow_rawPrefix]

private theorem marginalRows_eq (j : ℕ) : marginalRows j = marginalFormula j := by
  funext n
  unfold marginalRows
  by_cases h : j < 3
  · have he : marginalPrefix j = rawPrefix (marginalFormula j) := marginalPrefix_eq ⟨j, h⟩
    rw [he, prefixRow_rawPrefix]
  · cases j with
    | zero => omega
    | succ j =>
      cases j with
      | zero => omega
      | succ j =>
        cases j with
        | zero => omega
        | succ j => rfl

private def shiftedRows (rows : ℕ → List ℚ) (terms : ℕ) (center : ℚ) (m : ℕ) :
    List ℚ :=
  coeffSum (fun j =>
    let n := m + j
    coeffScale ((n.choose m : ℚ) * center ^ (n - m)) (rows n)) (terms - m)

private theorem jointModel_eq (i : Fin 3) (upper radius width center : ℚ)
    (terms order : ℕ) (H X : Model) :
    shortJointClosedQuadratureModel i upper radius width center terms order H X =
      ((Model.series order (fun m ↦ Model.horner
          (shiftedRows (jointRows i) terms center m) H) X).widen
        (quadratureShiftBound upper radius width (jointRows i) terms order)).widen
          (jointDensityTailBound (shortJointDensityRow i) upper radius terms) := by
  rw [jointRows_eq]
  rfl

private theorem marginalModel_eq (upper radius width center : ℚ)
    (j terms order : ℕ) (H X : Model) :
    marginalClosedQuadratureModel upper radius width center j terms order H X =
      ((Model.series order (fun m ↦ Model.horner
          (shiftedRows (marginalRows j) terms center m) H) X).widen
        (quadratureShiftBound upper radius width (marginalRows j) terms order)).widen
          (marginalQuadratureTailBound upper radius j terms) := by
  rw [marginalRows_eq]
  rfl

attribute [scoped cbv_eval] jointModel_eq marginalModel_eq

scoped cbv_simproc cbv_eval stageShiftedCachedRow (shiftedRows _ _ _ _) :=
  stageLiteral (List Rat) (limitStatementSize := true)

scoped cbv_simproc cbv_eval stageParameterRow (quadratureParameterRow _ _ _ _) :=
  stageLiteral (List Rat) (limitStatementSize := true)
scoped cbv_simproc cbv_eval stageShiftedRow (shiftedQuadratureParameterRow _ _ _ _ _ _) :=
  stageLiteral (List Rat) (limitStatementSize := true)
scoped cbv_simproc cbv_eval stageShiftBound (quadratureShiftBound _ _ _ _ _ _) :=
  stageLiteral Rat (limitStatementSize := true)
scoped cbv_simproc cbv_eval stageExpMoment (shortExpMomentBound _ _ _ _ _ _ _) :=
  stageLiteral Rat (limitStatementSize := true)

scoped cbv_simproc cbv_eval stageMul (Model.mul _ _) := stageOnModels 2 (stageModel (limitStatementSize := true))
scoped cbv_simproc cbv_eval stageAdd (Model.add _ _) := stageOnModels 2 (stageModel (limitStatementSize := true))
scoped cbv_simproc cbv_eval stageSub (Model.sub _ _) := stageOnModels 2 (stageModel (limitStatementSize := true))
scoped cbv_simproc cbv_eval stageOfRat (Model.ofRat _) := (stageModel (limitStatementSize := true))
scoped cbv_simproc cbv_eval stageWiden (Model.widen _ _) := stageOnModels 1 (stageModel (limitStatementSize := true))
scoped cbv_simproc cbv_eval stageLower (Model.lower _) := stageOnModels 1 (stageLiteral Int (limitStatementSize := true))
scoped cbv_simproc cbv_eval stageAbsUpper (Model.absUpper _) := stageOnModels 1 (stageLiteral Nat (limitStatementSize := true))
scoped cbv_simproc cbv_eval stageCenter (CompactTaylorModel.Model.center _) :=
  stageOnModels 1 (stageLiteral Rat (limitStatementSize := true))
scoped cbv_simproc cbv_eval stageCoeffScale (coeffScale _ _) := stageLiteral (List Rat) (limitStatementSize := true)
scoped cbv_simproc cbv_eval stageCoeffAdd (coeffAdd _ _) := stageLiteral (List Rat) (limitStatementSize := true)

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
