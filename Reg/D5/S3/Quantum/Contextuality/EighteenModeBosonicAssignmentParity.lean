import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity
import Reg.Support.DependentFamily

/-! Source-bound audit of the particle-number parity in the assignment equivalence. -/

namespace Reg.D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity

open _root_.D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Decide parity by structural recursion on the particle number. -/
private def evenDecision : (n : ℕ) → Decidable (Even n) :=
  Nat.rec (motive := fun n => Decidable (Even n)) (isTrue ⟨0, rfl⟩)
    (fun n ih =>
      letI : Decidable (Even n) := ih
      decidable_of_iff (¬ Even n)
        (by simpa only [Nat.succ_eq_add_one] using (Nat.even_add_one (n := n)).symm))

/-- Observe the evenness predicate at the particle-number coordinate. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => @decide (Even n) (evenDecision n))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

/-- Retain every particle number and the complete assignment-existence condition. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, (∃ v, IsNoncontextualAssignment n v) ↔ R.readout () () n = true

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero : ∃ v, IsNoncontextualAssignment 0 v := (result 0).mpr (by simp)
  have hbad := (h 0).mp hzero
  exact Bool.noConfusion hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change @decide (Even (0 : ℕ)) (evenDecision 0) ≠
    @decide (Even (1 : ℕ)) (evenDecision 1)
  decide

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [claim, actual, realize]
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ n => @decide (Even n) (evenDecision n))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity
      name := `D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity
