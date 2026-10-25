import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation
import Reg.Support.DependentFamily

/-! Source-bound order-family audit for complete native transcript compensation. -/

open LeanInformationAudit
open _root_.D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators
noncomputable section
namespace Reg.D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation

namespace Compensation

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => n + 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def theoremLaw (R : Realization signature) : Prop :=
  ∀ (rho : ℚ) (_hrho : 0 < rho) (w : List Command),
    ∃ (epsilon : ℚ) (s : NativeSource) (z : Fin s.order → ℚ),
      0 < epsilon ∧ epsilon ≤ 1 / 8 ∧
      s.order = R.readout () () (tickCount w) ∧ InBall rho z ∧
      (∑ i, |z i|) < rho ∧
      run s.matrix z w = run reference (fun _ => 0) w ∧
      (s.matrix ^ 2) 0 0 = (1 / 2 : ℚ) ^ 2 + epsilon ^ 2

abbrev arena : Arena where
  signature := signature
  Law := theoremLaw

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨epsilon, s, z, _, _, horder, _⟩ := h 1 zero_lt_one []
  change s.dimension + 1 = 0 at horder
  omega

def family : Registration arena (type_of% @small_entry_complete_transcript_compensation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨small_entry_complete_transcript_compensation, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@small_entry_complete_transcript_compensation)
    (type_of% (realize signature (fun _ _ n => n + 2) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.small_entry_complete_transcript_compensation.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.Compensation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n + 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "body", "arg",
        "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family

end Compensation


namespace Admission

abbrev signature : Signature where
  Params := Σ _rho : ℚ, NativeSource
  State p := Fin p.2.order → ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ∑ i, (z i : ℝ) ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => (p.1 : ℝ) ^ 2 + 1) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, referenceSource⟩, (fun _ => 0), (fun _ => 2), ?_⟩
  norm_num [actual, realize, InBall, NativeSource.order, referenceSource]

end Admission

universe u v

namespace Deterministic

def theoremLaw (R : Realization Admission.signature) : Prop :=
  ∀ (rho : ℚ) (_hrho : 0 < rho) (L : Type u) (E : Type v)
    (p : Controller L E) (initial : L) (target : AcquisitionTarget E),
    ¬ (∀ (s : NativeSource) (z : Fin s.order → ℚ),
      (0 ≤ rho ∧ R.readout () ⟨rho, s⟩ z ≤ (rho : ℝ) ^ 2) →
      (∃ w e, Successful p s.matrix initial z w e) ∧
        ∀ w e, Successful p s.matrix initial z w e →
          target.Correct s (finalState s.matrix z w) e)

abbrev arena : Arena where
  signature := Admission.signature
  Law := theoremLaw.{u,v}

private theorem actual_law : arena.{u,v}.Law Admission.actual := by
  simpa only [theoremLaw, Admission.actual, realize] using
    (@no_deterministic_exact_acquisition.{u,v})

private theorem rejected_law : ¬ arena.{u,v}.Law Admission.rejected := by
  intro h
  have hh := h 1 zero_lt_one (ULift.{u} Unit) (ULift.{v} Unit)
    (fun _ => Decision.halt (ULift.up ())) (ULift.up ())
    (.nativeOrder (fun _ => 1))
  apply hh
  intro s z hz
  simp [Admission.rejected, realize] at hz
  linarith

def family : Registration arena.{u,v} (type_of% @no_deterministic_exact_acquisition.{u,v}) where
  actual := Admission.actual
  bridge := by simp only [theoremLaw, Admission.actual, realize]
  variation := ⟨actual_law, Admission.rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨Admission.rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := Admission.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@no_deterministic_exact_acquisition.{u,v})
    (type_of% (realize Admission.signature
      (fun _ _ z => ∑ i, (z i : ℝ) ^ 2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.no_deterministic_exact_acquisition.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.Deterministic.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Admission.signature
    (fun _ _ z => ∑ i, (z i : ℝ) ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation
    definition := none
    coordinates := #[0, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "domain", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family

end Deterministic

namespace Fair

def theoremLaw (R : Realization Admission.signature) : Prop :=
  ∀ (rho : ℚ) (_hrho : 0 < rho) (L : Type u) (E : Type v)
    (p : BitController L E) (initial : L) (target : AcquisitionTarget E),
    ¬ (∀ (s : NativeSource) (z : Fin s.order → ℚ),
      (0 ≤ rho ∧ R.readout () ⟨rho, s⟩ z ≤ (rho : ℝ) ^ 2) →
      fairMeasure (finiteSuccess p initial s z)ᶜ = 0 ∧
        fairMeasure (errorEvent p initial target s z) = 0)

abbrev arena : Arena where
  signature := Admission.signature
  Law := theoremLaw.{u,v}

private theorem actual_law : arena.{u,v}.Law Admission.actual := by
  simpa only [theoremLaw, Admission.actual, realize] using
    (@no_fair_zero_error_exact_acquisition.{u,v})

private theorem rejected_law : ¬ arena.{u,v}.Law Admission.rejected := by
  intro h
  have hh := h 1 zero_lt_one (ULift.{u} Unit) (ULift.{v} Unit)
    (fun _ => BitDecision.halt (ULift.up ())) (ULift.up ())
    (.nativeOrder (fun _ => 1))
  apply hh
  intro s z hz
  simp [Admission.rejected, realize] at hz
  linarith

def family : Registration arena.{u,v} (type_of% @no_fair_zero_error_exact_acquisition.{u,v}) where
  actual := Admission.actual
  bridge := by simp only [theoremLaw, Admission.actual, realize]
  variation := ⟨actual_law, Admission.rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨Admission.rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := Admission.dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@no_fair_zero_error_exact_acquisition.{u,v})
    (type_of% (realize Admission.signature
      (fun _ _ z => ∑ i, (z i : ℝ) ^ 2)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.no_fair_zero_error_exact_acquisition.__information_unit
  realizationName := `Reg.D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation.Fair.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨family.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Admission.signature
    (fun _ _ z => ∑ i, (z i : ℝ) ^ 2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation
    definition := none
    coordinates := #[0, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg",
        "body", "body", "domain", "arg", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family

end Fair

end Reg.D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation
