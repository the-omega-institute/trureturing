import Reg.Support.SourceSelection
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.HomologicalAlgebra.AcyclicCarrier

/-! Dependent-family realization of the primitive-choice sequence law. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.HomologicalAlgebra.AcyclicCarrier
noncomputable section
universe s

structure SequenceParameters where
  State : ℕ → Type s
  initial : State 0 → Prop
  step : ∀ m, State m → State (m+1) → Prop

abbrev sequenceSignature : Signature where
  Params := SequenceParameters.{s}
  State := fun p => ∀ m, p.State m
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def sequenceActual : Realization sequenceSignature := realize sequenceSignature
  (fun _ p seq => p.initial (seq 0) ∧ ∀ m, p.step m (seq m) (seq (m+1)))
  (fun e => nomatch e)
def sequenceRejected : Realization sequenceSignature := realize sequenceSignature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev sequenceArena : Arena where
  signature := sequenceSignature
  Law obs := ∀ (State : ℕ → Type s) (I : State 0 → Prop)
    (R : ∀ m, State m → State (m+1) → Prop),
    (∃ s : State 0, I s) → (∀ m (s : State m), ∃ s' : State (m+1), R m s s') →
    ∃ seq : ∀ m, State m, obs.readout () ⟨State,I,R⟩ seq

private theorem sequence_actual_law : sequenceArena.Law sequenceActual := by
  intro State I R h0 h
  exact _root_.D5.S3.HomologicalAlgebra.AcyclicCarrier.exists_sequence State I R h0 h

private theorem sequence_rejected_law : ¬ sequenceArena.Law (sequenceRejected : Realization sequenceSignature.{s}) := by
  intro h
  obtain ⟨seq, hseq⟩ := h (fun _ => ULift.{s} Unit) (fun _ => True) (fun _ _ _ => True)
    ⟨⟨()⟩, trivial⟩ (fun _ _ => ⟨⟨()⟩, trivial⟩)
  exact hseq

def sequenceRegistration : Registration sequenceArena.{s} (sequenceArena.Law sequenceActual) where
  actual := sequenceActual
  bridge := Iff.rfl
  variation := ⟨sequence_actual_law, sequenceRejected, sequence_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨sequenceRejected, ?_, rfl, sequence_rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨fun _ => ULift.{s} Bool, fun b => b.down = true, fun _ _ _ => True⟩,
      (fun _ => ⟨true⟩), (fun _ => ⟨false⟩), ?_⟩
    change (true = true ∧ ∀ m : ℕ, True) ≠ (false = true ∧ ∀ m : ℕ, True)
    simp

noncomputable def sequence_contract : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.HomologicalAlgebra.AcyclicCarrier.exists_sequence.{s})
    (type_of% (realize sequenceSignature.{s}
      (fun _ p seq => p.initial (seq 0) ∧ ∀ m, p.step m (seq m) (seq (m+1)))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.HomologicalAlgebra.AcyclicCarrier.sequence_unit
  realizationName := `Reg.D5.S3.HomologicalAlgebra.AcyclicCarrier.sequenceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨sequenceArena.{s}⟩
  objectArena := .source ⟨sequenceArena.{s}⟩
  catalog := Lean.Name.anonymous
  options := #[]
  localNames := false
  realization := .source sequenceArena.{s} ⟨sequenceRegistration.{s}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sequenceSignature.{s}
    (fun _ p seq => p.initial (seq 0) ∧ ∀ m, p.step m (seq m) (seq (m+1)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.HomologicalAlgebra.AcyclicCarrier
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
}
end
end Reg.D5.S3.HomologicalAlgebra.AcyclicCarrier
