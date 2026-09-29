import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause

/- Full original laws transported to a parameterized family. These support proofs
are not registration certificates: source-selection acceptance is tested separately. -/
namespace Reg.Support.LegacyRelations.Preemption
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open _root_.D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause

abbrev signature : Signature where
  Params := Unit
  State _ := PreemptionTrace
  Role := PreemptionReadout
  finiteRole := inferInstance
  nonemptyRole := ⟨.cutEnd⟩
  Output i _ := match i with
    | .cutEnd => Bool
    | .cutCause => Option Mechanism
    | .admitAThenB => Bool
    | .admitBThenA => Bool
  Anchor := PreemptionAnchor
  finiteAnchor := inferInstance

def toLegacy (r : Realization signature) :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization preemptionSignature where
  readout i := r.readout i ()
  anchor i := r.anchor i ()

/-- The Unit parameter changes no realization: both directions are inverse. -/
def fromLegacy (r :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization preemptionSignature) :
    Realization signature :=
  realize signature (fun i _ => r.readout i) (fun i _ => r.anchor i)

theorem to_from_legacy (r :
    _root_.D5.S3.ConceptDynamics.InformationEscape.PrimitiveRealization preemptionSignature) :
    toLegacy (fromLegacy r) = r := by
  cases r
  rfl

theorem from_to_legacy (r : Realization signature) : fromLegacy (toLegacy r) = r := by
  cases r with
  | mk readout anchor =>
    congr 1 <;> funext i p <;> cases p <;> rfl

def arena : Arena := ⟨signature, fun r =>
  r.readout .admitAThenB () (r.anchor .aThenB ()) = true ∧
    r.readout .admitBThenA () (r.anchor .bThenA ()) = true ∧
    r.readout .cutEnd () (r.anchor .aThenB ()) = r.readout .cutEnd () (r.anchor .bThenA ()) ∧
    r.readout .cutCause () (r.anchor .aThenB ()) ≠ r.readout .cutCause () (r.anchor .bThenA ()) ∧
    ¬ ∃ recover : Bool → Option Mechanism, r.readout .cutCause () = recover ∘ r.readout .cutEnd ()⟩

def actual : Realization signature :=
  realize signature (fun i _ => match i with
    | .cutEnd => endState
    | .cutCause => activeCause
    | .admitAThenB => fun trace => decide (IsOrderedPreemption trace .shooterA .shooterB)
    | .admitBThenA => fun trace => decide (IsOrderedPreemption trace .shooterB .shooterA))
    (fun i _ => match i with | .aThenB => aThenB | .bThenA => bThenA)

theorem full_law_transport (r : Realization signature) :
    arena.Law r ↔ endStateOmitsPreemptingCauseArena.Law (toLegacy r) := Iff.rfl

theorem bridge : EndStateOmitsPreemptingCauseStatement ↔ arena.Law actual :=
  end_state_omits_preempting_cause_realization.equivalence

def without_cutEnd : Realization signature where
  readout i _ := match i with
    | .cutEnd => fun trace => decide (trace = aThenB)
    | .cutCause => endStateOmitsPreemptingCauseRealization.readout .cutCause
    | .admitAThenB => endStateOmitsPreemptingCauseRealization.readout .admitAThenB
    | .admitBThenA => endStateOmitsPreemptingCauseRealization.readout .admitBThenA
  anchor := actual.anchor

def without_cutCause : Realization signature where
  readout i _ := match i with
    | .cutEnd => endStateOmitsPreemptingCauseRealization.readout .cutEnd
    | .cutCause => fun _ => none
    | .admitAThenB => endStateOmitsPreemptingCauseRealization.readout .admitAThenB
    | .admitBThenA => endStateOmitsPreemptingCauseRealization.readout .admitBThenA
  anchor := actual.anchor

def without_admitAThenB : Realization signature where
  readout i _ := match i with
    | .cutEnd => endStateOmitsPreemptingCauseRealization.readout .cutEnd
    | .cutCause => endStateOmitsPreemptingCauseRealization.readout .cutCause
    | .admitAThenB => fun _ => false
    | .admitBThenA => endStateOmitsPreemptingCauseRealization.readout .admitBThenA
  anchor := actual.anchor

def without_admitBThenA : Realization signature where
  readout i _ := match i with
    | .cutEnd => endStateOmitsPreemptingCauseRealization.readout .cutEnd
    | .cutCause => endStateOmitsPreemptingCauseRealization.readout .cutCause
    | .admitAThenB => endStateOmitsPreemptingCauseRealization.readout .admitAThenB
    | .admitBThenA => fun _ => false
  anchor := actual.anchor

theorem rejects_cutEnd : ¬ arena.Law without_cutEnd := by
  intro h
  have bad := h.2.2.1
  have different : (decide (aThenB = aThenB)) ≠ decide (bThenA = aThenB) := by decide
  exact different bad

theorem rejects_cutCause : ¬ arena.Law without_cutCause := by
  intro h
  exact h.2.2.2.1 rfl

theorem rejects_admitAThenB : ¬ arena.Law without_admitAThenB := by
  intro h
  exact Bool.noConfusion h.1

theorem rejects_admitBThenA : ¬ arena.Law without_admitBThenA := by
  intro h
  exact Bool.noConfusion h.2.1

def without_anchor (i : PreemptionAnchor) : Realization signature where
  readout := actual.readout
  anchor j := if j = i then fun _ _ => none else actual.anchor j

theorem rejects_anchor (i : PreemptionAnchor) : ¬ arena.Law (without_anchor i) := by
  intro h
  cases i with
  | aThenB =>
    have bad := h.1
    exact Bool.noConfusion bad
  | bThenA =>
    have bad := h.2.1
    exact Bool.noConfusion bad

theorem variation : Variation arena actual :=
  ⟨bridge.mp end_state_omits_preempting_cause, without_cutCause, rejects_cutCause⟩

theorem sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    cases i
    · refine ⟨without_cutEnd, ?_, rfl, rejects_cutEnd⟩
      intro j h
      cases j <;> first | exact (h rfl).elim | rfl
    · refine ⟨without_cutCause, ?_, rfl, rejects_cutCause⟩
      intro j h
      cases j <;> first | exact (h rfl).elim | rfl
    · refine ⟨without_admitAThenB, ?_, rfl, rejects_admitAThenB⟩
      intro j h
      cases j <;> first | exact (h rfl).elim | rfl
    · refine ⟨without_admitBThenA, ?_, rfl, rejects_admitBThenA⟩
      intro j h
      cases j <;> first | exact (h rfl).elim | rfl
  · intro i
    refine ⟨without_anchor i, rfl, ?_, rejects_anchor i⟩
    intro j h
    cases i <;> cases j <;> first | exact (h rfl).elim | rfl

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  · exact ⟨(), aThenB, (fun _ => none), by decide⟩
  · exact ⟨(), aThenB, bThenA, by decide⟩
  · exact ⟨(), aThenB, bThenA, by decide⟩
  · exact ⟨(), bThenA, aThenB, by decide⟩

def registration : Registration arena EndStateOmitsPreemptingCauseStatement where
  actual := actual
  bridge := bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

def selection : LeanInformationAudit.SourceSelection :=
  {
    owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
    coordinates := #[]
    readouts := #[
      {path := #["arg", "arg", "fn", "arg", "fn", "arg", "fn"], functionOperand := true},
      {path := #["arg", "arg", "arg", "fn", "arg", "fn", "arg", "fn"], functionOperand := true},
      {path := #["fn", "arg"], stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true},
      {path := #["arg", "fn", "arg"], stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true}] }

/-- The same complete-family witnesses supply the legacy finite catalog gates. -/
theorem finite_variation : LeanInformationAudit.FiniteLawVariation endStateOmitsPreemptingCauseArena := by
  obtain ⟨bad, rejected⟩ := variation.2
  exact ⟨toLegacy actual, toLegacy bad, variation.1, rejected⟩

theorem finite_sensitivity : LeanInformationAudit.FiniteSlotSensitivity endStateOmitsPreemptingCauseArena := by
  constructor
  · intro i
    obtain ⟨bad, fixed, anchors, rejected⟩ := sensitivity.1 i
    refine ⟨toLegacy actual, toLegacy bad, ?_, ?_, ?_⟩
    · intro j h
      exact congrFun (fixed j h) ()
    · intro j
      exact congrFun (congrFun anchors j) ()
    · exact ⟨fun _ => rejected, fun _ => variation.1⟩
  · intro i
    obtain ⟨bad, fixed, anchors, rejected⟩ := sensitivity.2 i
    refine ⟨toLegacy actual, toLegacy bad, ?_, ?_, ?_⟩
    · intro j
      exact congrFun (congrFun fixed j) ()
    · intro j h
      exact congrFun (anchors j h) ()
    · exact ⟨fun _ => rejected, fun _ => variation.1⟩

#print axioms registration
end Reg.Support.LegacyRelations.Preemption
