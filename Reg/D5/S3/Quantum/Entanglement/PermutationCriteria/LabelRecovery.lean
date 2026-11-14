import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

universe u

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Bool × Bool) (fun _ => (Bool × Bool) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (f g : ι → Bool × Bool),
    (∀ i, sameSide (f i) ↔ sameSide (g i)) →
    (∀ i j, pairDistance (f i) (f j) = pairDistance (g i) (g j)) →
    ∃ swap complement : Bool, ∀ i,
      R.readout () () (g i) (transform swap complement (f i))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨_, _, hbad⟩ := h
    (fun _ : ULift.{u} Unit => (false, false))
    (fun _ : ULift.{u} Unit => (false, false))
    (fun _ => Iff.rfl) (fun _ _ => rfl)
  exact hbad ⟨()⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (false, false), (true, false), ?_⟩
  intro he
  have hbad : ((true, false) : Bool × Bool) = (false, false) :=
    Eq.mp (congrFun he (false, false)) rfl
  cases hbad

def source_registration : Registration arena.{u} (type_of% @recover_labels.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recover_labels.{u}, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery.recover_labels.{u})
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery
