/- GID: D5/S3/ConceptDynamics/Communication/TruthfulnessSufficiencyIndependence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/TruthfulnessSufficiencyIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Truthful reporting and target sufficiency are independent factors. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-22):
   * Current-tree searches for true and sent report mechanisms, report
     sufficiency, and honesty-sufficiency independence found no exact family
     primitive. `ProvenanceReport` concerns audit evidence for one value and
     has neither state-indexed mechanisms nor target factorization.
   * Pinned Mathlib has function equality and Boolean discrimination but no
   theorem packaging the source reporting conditions. `Bool.false_ne_true`
     is applied directly in the four concrete profile checks below.
   * Loogle returned no hit for "report sufficiency". LeanSearch returned only
     conditional probability-independence declarations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.TruthfulnessSufficiencyIndependence

/-- The source reporting primitives: a target, a truthful report mechanism,
the mechanism actually sent, and a decoder for report messages. -/
structure ReportProfile (State Message Target : Type*) where
  target : State -> Target
  trueReport : State -> Message
  sentReport : State -> Message
  decode : Message -> Target

/-- If the sent and truthful mechanisms agree and the truthful mechanism is
sufficient for the target, then the sent mechanism is sufficient. Neither
honesty nor sufficiency implies the other: concrete profiles also realize
honest-only, sufficient-only, both, and neither. -/
theorem truthfulness_sufficiency_independence :
    (forall {State Message Target : Type*}
      (profile : ReportProfile State Message Target),
      profile.sentReport = profile.trueReport ->
      profile.target = profile.decode ∘ profile.trueReport ->
      profile.target = profile.decode ∘ profile.sentReport) ∧
    (exists profile : ReportProfile Bool Unit Bool,
      profile.sentReport = profile.trueReport ∧
        profile.target ≠ profile.decode ∘ profile.trueReport) ∧
    (exists profile : ReportProfile Bool Bool Bool,
      profile.sentReport ≠ profile.trueReport ∧
        profile.target = profile.decode ∘ profile.trueReport) ∧
    (exists profile : ReportProfile Bool Bool Bool,
      profile.sentReport = profile.trueReport ∧
        profile.target = profile.decode ∘ profile.trueReport) ∧
    (exists profile : ReportProfile Bool Bool Bool,
      profile.sentReport ≠ profile.trueReport ∧
        profile.target ≠ profile.decode ∘ profile.trueReport) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro State Message Target profile honest sufficient
    calc
      profile.target = profile.decode ∘ profile.trueReport := sufficient
      _ = profile.decode ∘ profile.sentReport :=
        congrArg (fun report => profile.decode ∘ report) honest.symm
  · let honestOnly : ReportProfile Bool Unit Bool :=
      { target := fun state => state
        trueReport := fun _ => ()
        sentReport := fun _ => ()
        decode := fun _ => false }
    refine ⟨honestOnly, rfl, ?_⟩
    intro sufficient
    exact Bool.false_ne_true (congrFun sufficient true).symm
  · let sufficientOnly : ReportProfile Bool Bool Bool :=
      { target := fun state => state
        trueReport := fun state => state
        sentReport := fun state => !state
        decode := fun message => message }
    refine ⟨sufficientOnly, ?_, rfl⟩
    intro honest
    exact Bool.false_ne_true (congrFun honest false).symm
  · let both : ReportProfile Bool Bool Bool :=
      { target := fun state => state
        trueReport := fun state => state
        sentReport := fun state => state
        decode := fun message => message }
    exact ⟨both, rfl, rfl⟩
  · let neither : ReportProfile Bool Bool Bool :=
      { target := fun state => state
        trueReport := fun _ => false
        sentReport := fun _ => true
        decode := fun message => message }
    refine ⟨neither, ?_, ?_⟩
    · intro honest
      exact Bool.false_ne_true (congrFun honest false).symm
    · intro sufficient
      exact Bool.false_ne_true (congrFun sufficient true).symm

#print axioms truthfulness_sufficiency_independence

end D5.S3.ConceptDynamics.Communication.TruthfulnessSufficiencyIndependence
