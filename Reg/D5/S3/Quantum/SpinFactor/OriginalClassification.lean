import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.SpinFactor.OriginalClassification

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
  escapeFrom := some E
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
  escapeFrom := some E
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
