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

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ParameterBounds.parameters
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x y => x < y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := ∀ low : Bool, 0 < rho ∧ rho < 1 ∧ 0 < chi ∧ chi < 1 ∧ 0 < h low ∧ h low < E low ∧ E low ≤ 1/4
abbrev arena : Arena where
  signature := signature
  Law R := ∀ low : Bool, R.readout () () 0 rho ∧ rho < 1 ∧ 0 < chi ∧ chi < 1 ∧ 0 < h low ∧ h low < E low ∧ E low ≤ 1/4
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact (hh false).1
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.parameters,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(0 : ℝ),(1 : ℝ),?_⟩
    intro he
    have bad : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) (by change (0 : ℝ) < 1; norm_num)
    exact (lt_irrefl (1 : ℝ)) bad
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.parameters)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x y => x < y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.parameters.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ParameterBounds.parameters.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x y => x < y) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[],
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "fn"], stateBinder := 0,
      functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ParameterBounds.parameters

namespace Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ParameterBounds.A_nonneg
abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)
def sourceStatement : Prop := 0 ≤ A false
abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (A false)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hh
  exact hh
def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S1.Digit.Infinite.ResetCodebook.A_nonneg,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨(),(-1 : ℝ),(0 : ℝ),?_⟩
    intro he
    have he' : (0 ≤ (-1 : ℝ)) = (0 ≤ (0 : ℝ)) := by
      simpa [actual, realize] using he
    have bad : (0 : ℝ) ≤ -1 := Eq.mpr he' (by norm_num)
    norm_num at bad
noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Digit.Infinite.ResetCodebook.A_nonneg)
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S1.Digit.Infinite.ResetCodebook.A_nonneg.__information_unit,
  realizationName := `Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ParameterBounds.A_nonneg.registration,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ x => 0 ≤ x) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Digit.Infinite.ResetCodebookFinite, definition := none, coordinates := #[],
    readouts := #[{
      path := #[], stateBinder := 0,
      functionOperand := false, stateOperand := some #["arg"], booleanPredicate := true }] },
  continuation := .unknown, familyRecord := none,
  options := #[] }
end Reg.D5.S1.Digit.Infinite.ResetCodebookFinite.ParameterBounds.A_nonneg
