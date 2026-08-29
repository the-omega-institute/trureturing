/- GID: D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticOverreachClosure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticOverreachClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Semantic overreach holds exactly when no licensed transport report closes it. -/

/- Library-search audit trail (2026-08-29):
   * Exact repository search
     `git grep -n -E 'semantic_overreach|SemanticOverreach|OverreachClosure|
     LicensedSemanticTransportReport|TransportReport' origin/dev --
     'D5/**/*.lean' 'Blueprint/**/*.scribe.cs'`
     found no result-bearing semantic-overreach declaration. It found only the
     frozen set-specialized `Transport.OverreachWithoutLicense` report carrier
     and package. That instance-level package is not imported into this general
     semantic module.
   * Statement-shape search
     `rg -n -i 'overreach.*closure|closure.*overreach|transport.*report|
     semantic.*overreach' D5 Blueprint --glob '*.lean' --glob '*.scribe.cs'
     --glob '*.md'`
     again found only that specialized frozen module and its mirror. Its report
     stores a `Concept` and `Set` scope, so it cannot instantiate the universe-
     polymorphic DECT 57.3 semantic frame used here.
   * Pinned-Mathlib exact-name search
     `rg -n 'semantic_overreach|SemanticOverreach|OverreachClosure|
     LicensedSemanticTransportReport' .lake/packages/mathlib/Mathlib
     .lake/packages/mathlib/Mathlib.lean --glob '*.lean'`
     returned no hit. A shape search found generic `and_iff_right` lemmas; the
     proof below instead exposes both directed implications explicitly. -/

import D5.S3.ConceptDynamics.DefinitionEscapeSemantics.SemanticTransportCertificateValidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.DefinitionEscape.Semantics

universe u v

/-- The DECT 54.3 report carrier: a claim, its reported domain, and the exact
condition retained by the report. -/
structure TransportReport (Claim Domain : Type u) where
  claim : Claim
  reportedDomain : Domain
  condition : Prop

/-- A report license carries one typed certificate for the same claim, source
domain, reported domain, and claim version, while retaining its premises
exactly as the report condition. -/
structure LicensedSemanticTransportReport
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (report : TransportReport Claim Domain)
    (J : Domain) where
  cert : TransportCert TruthReceipt NewDomainPrediction
  valid :
    ValidSemanticTransportCert S cert report.claim J report.reportedDomain
      (S.claimVersion report.claim)
  conditionExact :
    report.condition <-> cert.givenPremises /\ cert.transportAssumption

/-- The positive closure of an overreach allegation is the existence of a
licensed semantic transport report for that same report and source domain. -/
def OverreachClosure
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (report : TransportReport Claim Domain)
    (J : Domain) : Prop :=
  Nonempty (LicensedSemanticTransportReport S report J)

/-- A semantic report overreaches exactly when it strictly expands the claim's
source domain and no licensed report closes that expansion. -/
def SemanticOverreach
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (report : TransportReport Claim Domain)
    (J : Domain) : Prop :=
  SemanticStrictSubset S J report.reportedDomain /\
    S.claimScope report.claim = J /\
    Not (OverreachClosure S report J)

/-- Under the directed strict-expansion and exact source-scope hypotheses,
semantic overreach is equivalent to absence of a closing report license. -/
theorem semantic_overreach_iff_not_overreach_closure
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (report : TransportReport Claim Domain)
    (J : Domain)
    (strictExpansion : SemanticStrictSubset S J report.reportedDomain)
    (scopeExact : S.claimScope report.claim = J) :
    SemanticOverreach S report J <->
      Not (OverreachClosure S report J) := by
  constructor
  · intro overreach
    exact overreach.2.2
  · intro noClosure
    exact ⟨strictExpansion, scopeExact, noClosure⟩

#print axioms semantic_overreach_iff_not_overreach_closure

namespace ClosureWitness

private def frame :
    TransportSemanticFrame Unit Unit Unit Unit Bool Unit Bool Bool where
  claimAddress := fun _ => ()
  claimScope := fun _ => false
  claimVersion := fun _ => ()
  receiptMatches := fun _ _ _ _ => True
  claimOn := fun _ domain => domain = true
  inDomain := fun z domain => domain = true /\ z = true
  run := fun _ z => some z
  fails := fun _ _ result => result = true
  refutes := fun _ _ result _ => result = true

private def report : TransportReport Unit Bool where
  claim := ()
  reportedDomain := true
  condition := True

private def cert : TransportCert Unit Unit where
  oldReceipt := ()
  givenPremises := True
  transportAssumption := True
  falsifiablePrediction := ()

private def typedCertificate :
    SemanticTransportCertificate frame cert () false true () where
  strictExpansion := by
    simp [SemanticStrictSubset, SemanticNewOnly, frame]
  receiptBound := trivial
  conditionalTransport := by simp [frame]
  totalOnNewOnly := by
    intro z _newOnly
    exact ⟨z, rfl⟩
  refutingFailure := {
    failure := {
      evidence := true
      newOnly := by simp [SemanticNewOnly, frame]
      result := true
      observed := rfl
      failed := rfl
    }
    refutesClaim := rfl
  }

private def licensedReport :
    LicensedSemanticTransportReport frame report false where
  cert := cert
  valid := ⟨typedCertificate⟩
  conditionExact := by simp [report, cert]

/-- Domain-inhabitance witness used by the fidelity gate. -/
example : Bool := false

/-- Both hypotheses of the closure criterion hold in a concrete semantic
strict expansion. -/
example :
    SemanticStrictSubset frame false report.reportedDomain /\
      frame.claimScope report.claim = false := by
  constructor
  · simp [SemanticStrictSubset, SemanticNewOnly, frame, report]
  · rfl

/-- Positive control: a typed certificate with exact retained conditions closes
the concrete report. -/
example : OverreachClosure frame report false :=
  ⟨licensedReport⟩

/-- Consequently the same strictly expanded report is not an overreach. -/
example : Not (SemanticOverreach frame report false) := by
  intro overreach
  exact
    (semantic_overreach_iff_not_overreach_closure frame report false
      (by simp [SemanticStrictSubset, SemanticNewOnly, frame, report]) rfl).mp
      overreach ⟨licensedReport⟩

private def undefinedFrame :
    TransportSemanticFrame Unit Unit Unit Unit Bool Unit Bool Bool :=
  { frame with run := fun _ _ => none }

private theorem undefined_frame_has_no_closure :
    Not (OverreachClosure undefinedFrame report false) := by
  rintro ⟨licensed⟩
  obtain ⟨typed⟩ := licensed.valid
  obtain ⟨result, observed⟩ := typed.totalOnNewOnly true (by
    simp [SemanticNewOnly, undefinedFrame, frame, report])
  simp [undefinedFrame] at observed

/-- Negative control: removing every prediction result removes every license,
so the same strict expansion is a semantic overreach. -/
example : SemanticOverreach undefinedFrame report false :=
  (semantic_overreach_iff_not_overreach_closure undefinedFrame report false
    (by simp [SemanticStrictSubset, SemanticNewOnly, undefinedFrame, frame, report])
    rfl).mpr undefined_frame_has_no_closure

end ClosureWitness

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
