/- GID: D5/S3/ConceptDynamics/ProvenanceAdmissionCountermodel
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/ProvenanceAdmissionCountermodel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal report contents can carry provenance with opposite admission status. -/

import Mathlib.Data.Bool.Basic

/- Library-search audit trail (2026-08-21):
   * Searches of D5, the active branch, and `origin/dev` for certified reports,
     provenance validity, and equal-content admission found no canonical carrier
     or theorem to import. The source definition atom for certified reports is
     still open, so this is the first formal carrier in the family.
   * Pinned Mathlib has no report-provenance or epistemic-admission structure.
   Its exact theorem `Bool.false_ne_true` is applied directly to distinguish
     the verified and unverified signature fields below.
   * Generic Sigma and Subtype constructors are adjacent packaging tools; they
     do not construct the source evidence fields or the admission countermodel.
   * The `loogle` and `leansearch` executables were unavailable on PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ProvenanceAdmissionCountermodel

/-- Evidence recording how a report was produced. The fields are the source's
listed provenance primitives rather than a classifier chosen from the target
admission conclusion. -/
structure ProvenanceEvidence (Content : Type*) where
  producedContent : Content
  sourceAuthenticated : Bool
  observationDeviceCalibrated : Bool
  timestampAccepted : Bool
  procedureVerified : Bool
  intermediateProofChecked : Bool
  signatureVerified : Bool
  dependenciesCurrent : Bool
  preconditionSatisfied : Bool

/-- The source verification rule: the evidence must concern the reported
content and every named provenance check must pass. -/
def provenanceValid {Content : Type*} (evidence : ProvenanceEvidence Content)
    (content : Content) : Prop :=
  evidence.producedContent = content ∧
    evidence.sourceAuthenticated = true ∧
    evidence.observationDeviceCalibrated = true ∧
    evidence.timestampAccepted = true ∧
    evidence.procedureVerified = true ∧
    evidence.intermediateProofChecked = true ∧
    evidence.signatureVerified = true ∧
    evidence.dependenciesCurrent = true ∧
    evidence.preconditionSatisfied = true

/-- A report instance carries both its extensional content and the provenance
whose validity determines admission. -/
structure ProvenanceReport (Content : Type*) where
  content : Content
  provenance : ProvenanceEvidence Content

/-- Admission evaluates the source verification rule on the provenance carried
by this report instance. -/
def admitted {Content : Type*} (report : ProvenanceReport Content) : Prop :=
  provenanceValid report.provenance report.content

/-- Two reports can have equal extensional content and distinct provenance,
with the first admitted and the second rejected. Hence content equality does
not imply equality of their provenance-sensitive epistemic status. -/
theorem equal_content_does_not_determine_admission :
    ∃ first second : ProvenanceReport Bool,
      first.content = second.content ∧
        first.provenance ≠ second.provenance ∧
        admitted first ∧
        ¬ admitted second ∧
        ¬(admitted first ↔ admitted second) ∧
        ¬(first.content = second.content →
          (admitted first ↔ admitted second)) := by
  let verified : ProvenanceEvidence Bool :=
    { producedContent := false
      sourceAuthenticated := true
      observationDeviceCalibrated := true
      timestampAccepted := true
      procedureVerified := true
      intermediateProofChecked := true
      signatureVerified := true
      dependenciesCurrent := true
      preconditionSatisfied := true }
  let unsigned : ProvenanceEvidence Bool :=
    { producedContent := false
      sourceAuthenticated := true
      observationDeviceCalibrated := true
      timestampAccepted := true
      procedureVerified := true
      intermediateProofChecked := true
      signatureVerified := false
      dependenciesCurrent := true
      preconditionSatisfied := true }
  let first : ProvenanceReport Bool :=
    { content := false, provenance := verified }
  let second : ProvenanceReport Bool :=
    { content := false, provenance := unsigned }
  refine ⟨first, second, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · intro sameProvenance
    have signatureEquality : true = false := by
      simpa [first, second, verified, unsigned] using
        congrArg ProvenanceEvidence.signatureVerified sameProvenance
    exact Bool.false_ne_true signatureEquality.symm
  · simp [admitted, provenanceValid, first, verified]
  · simp [admitted, provenanceValid, second, unsigned]
  · simp [admitted, provenanceValid, first, second, verified, unsigned]
  · simp [admitted, provenanceValid, first, second, verified, unsigned]

/-- The concrete report-content domain is inhabited. -/
example : Bool := false

/-- The source evidence checks admit a concrete provenance-bearing report. -/
example : ∃ report : ProvenanceReport Bool, admitted report := by
  let evidence : ProvenanceEvidence Bool :=
    { producedContent := false
      sourceAuthenticated := true
      observationDeviceCalibrated := true
      timestampAccepted := true
      procedureVerified := true
      intermediateProofChecked := true
      signatureVerified := true
      dependenciesCurrent := true
      preconditionSatisfied := true }
  exact ⟨{ content := false, provenance := evidence }, by
    simp [admitted, provenanceValid, evidence]⟩

#print axioms equal_content_does_not_determine_admission

end D5.S3.ConceptDynamics.ProvenanceAdmissionCountermodel
