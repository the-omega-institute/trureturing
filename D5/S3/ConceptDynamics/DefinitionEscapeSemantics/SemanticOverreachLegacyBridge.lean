/- GID: D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticOverreachLegacyBridge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticOverreachLegacyBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Semantic overreach is exactly its legacy propositional image. -/

import D5.S3.ConceptDynamics.DefinitionEscapeSemantics.SemanticOverreachClosure

/- Library-search audit trail (2026-08-29):
   * Exact repository searches for `semantic_overreach_iff_overreach`,
     `SemanticOverreach` paired with `Overreach`, and an `Overreach` applied to
     `toLegacy` found no theorem discharging the 57.3-E bridge.
   * The only existing `Overreach` declaration is the frozen set-specialized
     `Transport.OverreachWithoutLicense` predicate. Its report, certificate,
     and semantics carriers differ from the universe-polymorphic DECT 54.3
     carriers already frozen in the imported semantic modules, so it cannot
     state this bridge.
   * Pinned Mathlib contains no domain-specific semantic-overreach, transport-
     license, or legacy-forgetful theorem. The proof below instead reuses the
     frozen 57.3-C certificate-validity equivalence at the sole license
     existential. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.DefinitionEscape.Semantics

universe u v

/-- The DECT 54.3 legacy overreach predicate. This is its sole universe-
polymorphic declaration; the older frozen transport module has incompatible
set-specialized report and certificate carriers. -/
def Overreach
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    (S :
      TransportSemantics TruthReceipt NewDomainPrediction Claim ContentAddress
        Domain Version NewEvidence)
    (report : TransportReport Claim Domain)
    (J : Domain) : Prop :=
  S.strictSubset J report.reportedDomain /\
    S.claimScope report.claim = J /\
    Not (Exists fun cert =>
      ValidTransportCert S cert report.claim J report.reportedDomain
          (S.claimVersion report.claim) /\
        (report.condition <->
          cert.givenPremises /\ cert.transportAssumption))

/-- Result-bearing semantic overreach is exactly the original DECT 54.3
propositional overreach predicate after the unique legacy forgetful map. -/
theorem semantic_overreach_iff_overreach
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (report : TransportReport Claim Domain)
    (J : Domain) :
    SemanticOverreach S report J <->
      Overreach (TransportSemanticFrame.toLegacy S) report J := by
  constructor
  · rintro ⟨strictExpansion, scopeExact, noSemanticLicense⟩
    refine ⟨strictExpansion, scopeExact, ?_⟩
    rintro ⟨cert, legacyValid, conditionExact⟩
    apply noSemanticLicense
    exact ⟨{
      cert := cert
      valid :=
        (valid_semantic_transport_cert_iff_valid_transport_cert S cert
          report.claim J report.reportedDomain
          (S.claimVersion report.claim)).mpr legacyValid
      conditionExact := conditionExact
    }⟩
  · rintro ⟨strictExpansion, scopeExact, noLegacyLicense⟩
    refine ⟨strictExpansion, scopeExact, ?_⟩
    rintro ⟨semanticLicense⟩
    apply noLegacyLicense
    exact ⟨semanticLicense.cert,
      (valid_semantic_transport_cert_iff_valid_transport_cert S
        semanticLicense.cert report.claim J report.reportedDomain
        (S.claimVersion report.claim)).mp semanticLicense.valid,
      semanticLicense.conditionExact⟩

#print axioms semantic_overreach_iff_overreach

namespace LegacyBridgeWitness

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

/-- Positive control: an exact typed license makes both independently anchored
overreach predicates false. -/
example :
    Not (SemanticOverreach frame report false) /\
      Not (Overreach (TransportSemanticFrame.toLegacy frame) report false) := by
  have noSemantic : Not (SemanticOverreach frame report false) := by
    intro semanticOverreach
    exact semanticOverreach.2.2 ⟨licensedReport⟩
  exact ⟨noSemantic, fun legacyOverreach =>
    noSemantic
      ((semantic_overreach_iff_overreach frame report false).mpr
        legacyOverreach)⟩

private def undefinedFrame :
    TransportSemanticFrame Unit Unit Unit Unit Bool Unit Bool Bool :=
  { frame with run := fun _ _ => none }

private theorem undefined_frame_has_no_closure :
    Not (OverreachClosure undefinedFrame report false) := by
  rintro ⟨license⟩
  obtain ⟨typed⟩ := license.valid
  obtain ⟨result, observed⟩ := typed.totalOnNewOnly true (by
    simp [SemanticNewOnly, undefinedFrame, frame, report])
  simp [undefinedFrame] at observed

/-- Negative control: removing every prediction result removes every license,
so both overreach predicates hold on the same strict expansion. -/
example :
    SemanticOverreach undefinedFrame report false /\
      Overreach (TransportSemanticFrame.toLegacy undefinedFrame)
        report false := by
  have semantic : SemanticOverreach undefinedFrame report false :=
    ⟨by
      simp [SemanticStrictSubset, SemanticNewOnly, undefinedFrame, frame,
        report],
      rfl,
      undefined_frame_has_no_closure⟩
  exact ⟨semantic,
    (semantic_overreach_iff_overreach undefinedFrame report false).mp semantic⟩

end LegacyBridgeWitness

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
