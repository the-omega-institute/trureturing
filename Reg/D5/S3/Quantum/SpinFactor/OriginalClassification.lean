import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.SpinFactor.OriginalClassification

section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
open WithLp
open scoped BigOperators ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers

abbrev signature : Signature where
  Params := Σ _ : Bool, E
  State _ := E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := E
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p b =>
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD
      (if p.1 then .plus else .minus) p.2 b) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

/-- The varied family occurs only in the original global correspondence hypothesis. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (opposite : Bool) (D : Relation),
    (∀ a b, D a b = R.readout () ⟨opposite, a⟩ b) →
      Consequences D ∧ MatrixInterfaces opposite D

private def ex : E := (0, ![1, 0, 0])
private def ey : E := (0, ![0, 1, 0])

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hnorm : vnorm ey.2 ≤ 1 := by
    norm_num [ey, vnorm,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.vnorm,
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot]
  let α : _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.Evaluation :=
    { mass := 1, vector := ey.2, positive := hnorm }
  have hb := (h false (fun _ _ => 0) (fun _ _ => rfl)).1.pb α ex ex ey
  norm_num [α,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.PB,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.squareReadout,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.phaseR,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.phaseS,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.evaluate, ex, ey,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.jordan,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.dot] at hb

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨false, ex⟩, 0, ey, ?_⟩
  intro h
  have hz := congrArg (fun a : E => a.2 2) h
  norm_num [actual, realize, ex, ey,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD,
    _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.cross] at hz

def family : Registration arena (type_of% (@same_D_consequences)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨same_D_consequences, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@same_D_consequences) (Realization signature) Type Unit := {
  unitName := `D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers.same_D_consequences.information_unit
  realizationName := `Reg.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p b =>
      _root_.D5.S3.Quantum.SpinFactor.OriginalDContract.crossD
        (if p.1 then .plus else .minus) p.2 b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalClassification
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "domain", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers

end
end

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.Quantum.SpinFactor.OriginalDContract
open _root_.D5.S3.Quantum.SpinFactor.OriginalClassification
open _root_.D5.S3.Quantum.Information.Pauli.OriginalSpinConsumers
  (Consequences MatrixInterfaces)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.SpinFactor.OriginalClassification

abbrev signature : Signature where
  Params := Unit
  State _ := E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := E → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem model_plus : P2 (crossD .plus) ∧ PB (crossD .plus) :=
  (complete_classification (crossD .plus)).mpr ⟨.plus, fun _ _ => rfl⟩

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, unit, ?_⟩
  intro h
  have hz : unit = (0 : E) := Eq.mp (congrFun h 0) rfl
  have hs := congrArg Prod.fst hz
  norm_num [unit] at hs

private theorem sensitivity (law : Realization signature → Prop)
    (hbad : ¬ law rejected) : Sensitivity ⟨signature, law⟩ actual := by
  refine ⟨fun i => ⟨rejected, ?_, rfl, hbad⟩, fun e => nomatch e⟩
  intro j hji
  exact (hji (Subsingleton.elim j i)).elim

namespace Classification

abbrev arena : Arena where
  signature := signature
  Law R := ∀ D : E → E → E, P2 D ∧ PB D ↔
    ∃ ε : Orientation, ∀ a b : E, R.readout () () (D a b) (crossD ε a b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, hh⟩ := (h (crossD .plus)).mp model_plus
  exact hh unit unit

def family : Registration arena (type_of% (@complete_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_classification, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_classification) (Realization signature) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalClassification.complete_classification.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalClassification.Classification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Classification

namespace ConsequencesAudit

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (D : E → E → E) (_ : P2 D) (_ : PB D),
    ∃ ε : Orientation,
      (ε = .plus ∨ ε = .minus) ∧
      (∀ a b : E, R.readout () () (D a b) (crossD ε a b)) ∧
      (Consequences D ∧ MatrixInterfaces (orientationBool ε) D)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨_, _, hh, _⟩ := h (crossD .plus) model_plus.1 model_plus.2
  exact hh unit unit

def family : Registration arena (type_of% (@complete_consequences)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨complete_consequences, rejected, rejected_law⟩
  sensitivity := sensitivity arena.Law rejected_law
  dependence := actual_dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@complete_consequences) (Realization signature) Type Unit where
  unitName := `D5.S3.Quantum.SpinFactor.OriginalClassification.complete_consequences.audit
  realizationName := `Reg.D5.S3.Quantum.SpinFactor.OriginalClassification.ConsequencesAudit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a = b)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinFactor.OriginalClassification
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "fn", "arg",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ConsequencesAudit

end Reg.D5.S3.Quantum.SpinFactor.OriginalClassification
