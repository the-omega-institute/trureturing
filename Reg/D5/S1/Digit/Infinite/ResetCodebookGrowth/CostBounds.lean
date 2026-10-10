import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Digit.Infinite.ResetCodebookWeighted
import Reg.Support.DependentFamily

open D5.S1.Digit.Infinite
open D5.S1.Digit.Infinite.ResetCodebook
open D5.S1.Digit.Infinite.ResetCodebook.Coding
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.FixedTailClosedBudget
open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Topology
noncomputable section

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.U_cost
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => max x (lambda-rho)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ D : ℝ, 0 ≤ D → D ≤ 1/4 → wordCost U sixColor (coord false D) ≤ max (lambda-g^2*D) (lambda-rho)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ D : ℝ, 0 ≤ D → D ≤ 1/4 → wordCost U sixColor (coord false D) ≤ R.readout () () (lambda-g^2*D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh 0 le_rfl (by norm_num)
  change wordCost U sixColor (coord false 0) ≤ -1 at he
  have hn : 0 ≤ wordCost U sixColor (coord false 0) := by
    simp only [U,sixColor,wordCost]
    positivity
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.U_cost,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),lambda-rho,lambda-rho+1,?_⟩
    change max (lambda-rho) (lambda-rho) ≠ max (lambda-rho+1) (lambda-rho)
    rw [max_self,max_eq_left (by linarith)]
    linarith
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.U_cost)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => max x (lambda-rho)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.U_cost.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.U_cost.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => max x (lambda-rho)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookGrowth, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.U_cost

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.V_cost
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => max x (lambda-rho)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)
def sourceStatement : Prop := ∀ D : ℝ, 0 ≤ D → D ≤ 1/4 → wordCost V sixColor (coord true D) ≤ max (lambda-g^2*D) (lambda-rho)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ D : ℝ, 0 ≤ D → D ≤ 1/4 → wordCost V sixColor (coord true D) ≤ R.readout () () (lambda-g^2*D)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  have he := hh 0 le_rfl (by norm_num)
  change wordCost V sixColor (coord true 0) ≤ -1 at he
  have hn : 0 ≤ wordCost V sixColor (coord true 0) := by
    simp only [V,sixColor,wordCost]
    positivity
  linarith
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_cost,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),lambda-rho,lambda-rho+1,?_⟩
    change max (lambda-rho) (lambda-rho) ≠ max (lambda-rho+1) (lambda-rho)
    rw [max_self,max_eq_left (by linarith)]
    linarith
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.V_cost)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => max x (lambda-rho)) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.V_cost.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.V_cost.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => max x (lambda-rho)) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookGrowth, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "arg"], stateBinder := 0,
      functionOperand := false, stateOperand := some #["fn", "arg"], booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.V_cost

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.C_cost
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ z : ℝ, |z-c0| ≤ 1/4 → wordCost C twentyColor z ≤ lambda-rho
abbrev arena : Arena where
  signature := signature
  Law R := ∀ z : ℝ, |z-c0| ≤ 1/4 → R.readout () () (wordCost C twentyColor z) (lambda-rho)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh c0 (by simp)
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_cost,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    intro he
    have bad : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at bad
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.C_cost)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.C_cost.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.C_cost.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookGrowth, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "body", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookGrowth.CostBounds.C_cost

