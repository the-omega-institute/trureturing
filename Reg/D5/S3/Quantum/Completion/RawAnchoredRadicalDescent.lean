import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Completion.RawAnchoredRadicalDescent

/-! Source registration for the actual anchored radical descent theorem. -/

namespace Reg.D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
open _root_.D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
open _root_.D5.S3.Quantum.Completion.RawThreePhaseDescent
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ULift.{u} Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ULift.{u} Bool → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := (type_of% @raw_anchored_radical_descent.{u}) ∧
    R.readout () () (ULift.up false) (ULift.up false)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h.2

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨(), ULift.up false, ULift.up true, ?_⟩
  intro he
  have hval := congrFun he (ULift.up false : ULift.{u} Bool)
  have hbad : (True : Prop) = False := by
    simpa [actual, realize] using hval
  exact Eq.mp hbad True.intro

private theorem source_sensitivity :
    Sensitivity (arena.{u}) (actual : Realization signature.{u}) := by
  constructor
  · intro i
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · funext e
      exact nomatch e
  · intro i
    exact nomatch i

def source_registration : Registration arena.{u}
    (type_of% @raw_anchored_radical_descent.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h
      exact ⟨h, rfl⟩
    · intro h
      exact h.1
  variation := ⟨⟨@raw_anchored_radical_descent.{u}, rfl⟩, rejected, rejected_law⟩
  sensitivity := source_sensitivity
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@raw_anchored_radical_descent.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.RawAnchoredRadicalDescent.raw_anchored_radical_descent.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.RawAnchoredRadicalDescent.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
