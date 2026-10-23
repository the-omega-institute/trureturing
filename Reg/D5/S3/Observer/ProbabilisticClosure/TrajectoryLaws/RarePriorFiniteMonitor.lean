import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := List Letter
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Monitor
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ w => scanWord monitorInitial w) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => Monitor.sink) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ w : List Letter,
    R.readout () () w = .accepted ↔ ∃ n : ℕ, 375 ≤ n ∧ w = blocks n ++ latchWord

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (blocks 375 ++ latchWord)).mpr ⟨375, le_rfl, rfl⟩
  cases he

set_option maxRecDepth 4096 in
def registration : Registration arena
    (∀ w : List Letter, scanWord monitorInitial w = .accepted ↔
      ∃ n : ℕ, 375 ≤ n ∧ w = blocks n ++ latchWord) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨whole_word_recognition, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨(), [], blocks 375 ++ latchWord, ?_⟩
    intro h
    dsimp only [actual, realize] at h
    have he : scanWord monitorInitial (blocks 375 ++ latchWord) = .accepted :=
      (whole_word_recognition _).mpr ⟨375, le_rfl, rfl⟩
    have h0 : scanWord monitorInitial [] = .block 0 0 := rfl
    rw [h0, he] at h
    cases h

noncomputable def whole_word_registration : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@whole_word_recognition)
    (type_of% (realize signature (fun _ _ w => scanWord monitorInitial w) (fun e => nomatch e)))
    Type Unit := {
  unitName := `RarePriorFiniteMonitor.whole_word_recognition.__information_unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ w => scanWord monitorInitial w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms registration
end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorFiniteMonitor
