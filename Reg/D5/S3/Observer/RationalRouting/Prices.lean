import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.RationalRouting.Prices

/-! Exact source-owned variation and dependence for actual rational acquisition. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.RationalRouting

noncomputable section
namespace Reg.D5.S3.Observer.RationalRouting.Prices

abbrev signature : Signature where
  Params := View
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ V h => Feasible V h false) Empty.elim

def rejected : Realization signature := realize signature (fun _ _ _ => True) Empty.elim

theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨View.B,0,2,?_⟩
  intro he
  have yes : actual.readout () View.B 2 := (original_view_action_prices View.B).1
  have bad : Feasible View.B 0 false := Eq.mpr he yes
  have h := (original_view_action_prices View.B).2.1 0 bad
  omega

def arena : Arena where
  signature := signature
  Law R := ∀ V : View,
    Feasible V 2 false ∧ (∀ h, R.readout () V h → 2 ≤ h) ∧
    Feasible V 4 true ∧ (∀ h, Feasible V h true → 4 ≤ h)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := (h View.B).2.1 0 trivial
  exact (by decide : ¬ (2 : ℕ) ≤ 0) bad

def family : Registration arena (type_of% (@original_view_action_prices)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_view_action_prices,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_view_action_prices) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.RationalRouting.original_view_action_prices.__information_unit
  realizationName := `Reg.D5.S3.Observer.RationalRouting.Prices.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ V h => Feasible V h false) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.RationalRouting.Prices
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","arg","fn","arg","body","domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration

end Reg.D5.S3.Observer.RationalRouting.Prices
