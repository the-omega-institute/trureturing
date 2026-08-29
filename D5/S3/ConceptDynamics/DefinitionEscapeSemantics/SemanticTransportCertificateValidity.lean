/- GID: D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticTransportCertificateValidity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticTransportCertificateValidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Typed transport certificates are exactly their legacy propositional closure. -/

/- Library-search audit trail (2026-08-29):
   * Exact repository search for `ValidSemanticTransportCert`,
     `SemanticTransportCertificate`, and a transport-frame `toLegacy` map found
     no declaration in D5 or Blueprint.
   * Statement-shape searches for an iff between a result-bearing certificate
     and a five-clause Prop certificate found only the frozen strict-subset and
     refutation-projection modules imported below. Their generic frame,
     new-only relation, run-definedness, run-failure, and failure witness are
     reused directly.
   * The frozen `TransportCertificateValidity.ValidTransportCert` was inspected
     separately. It is an older `Set Point` specialization without the 54.3
     strict-subset clause, so it cannot replace the universe-polymorphic legacy
     skeleton transcribed here.
   * Pinned Mathlib searches found `Option.some.inj` and `Option.some.injEq`, but
     no domain-specific transport certificate or equivalence. LeanSearch was
     reachable, and its exact-name query returned no result. -/

import D5.S3.ConceptDynamics.DefinitionEscapeSemantics.TransportRefutationProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.DefinitionEscape.Semantics

universe u v

/-- The DECT 54.3 legacy carrier. Its prediction field is interpreted by a
result-bearing semantic frame rather than replaced by a second prediction. -/
structure TransportCert
    (TruthReceipt NewDomainPrediction : Type u) where
  oldReceipt : TruthReceipt
  givenPremises : Prop
  transportAssumption : Prop
  falsifiablePrediction : NewDomainPrediction

/-- The DECT 54.3 propositional interface to which result-bearing semantics are
forgotten. This is local to the adjudication vocabulary because the older
frozen transport module has a different, set-specialized carrier. -/
structure TransportSemantics
    (TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u) where
  claimAddress : Claim -> ContentAddress
  claimScope : Claim -> Domain
  claimVersion : Claim -> Version
  receiptMatches : TruthReceipt -> ContentAddress -> Domain -> Version -> Prop
  strictSubset : Domain -> Domain -> Prop
  claimOn : Claim -> Domain -> Prop
  inNewOnlyDomain : NewEvidence -> Domain -> Domain -> Prop
  predictionDefined : NewDomainPrediction -> NewEvidence -> Prop
  predictionFails : NewDomainPrediction -> NewEvidence -> Prop
  refutes : NewEvidence -> TransportCert TruthReceipt NewDomainPrediction ->
    Claim -> Prop

/-- The result-bearing interpretation of refutation for the DECT 54.3
certificate carrier. -/
def SemanticRefutes
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (z : NewEvidence)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim) : Prop :=
  Exists fun result =>
    S.run cert.falsifiablePrediction z = some result /\
      S.refutes cert.falsifiablePrediction z result claim

namespace TransportSemanticFrame

/-- The unique forgetful map from result-bearing transport semantics to the
DECT 54.3 propositional interface. -/
def toLegacy
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      D5.S3.ConceptDynamics.DefinitionEscape.Semantics.TransportSemanticFrame
        TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
        NewEvidence PredictionResult) :
    TransportSemantics TruthReceipt NewDomainPrediction Claim ContentAddress
      Domain Version NewEvidence where
  claimAddress := S.claimAddress
  claimScope := S.claimScope
  claimVersion := S.claimVersion
  receiptMatches := S.receiptMatches
  strictSubset := SemanticStrictSubset S
  claimOn := S.claimOn
  inNewOnlyDomain := SemanticNewOnly S
  predictionDefined := SemanticPredictionDefined S
  predictionFails := SemanticPredictionFails S
  refutes := SemanticRefutes S

end TransportSemanticFrame

/-- The original five-clause propositional validity predicate from DECT 54.3. -/
def ValidTransportCert
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    (S :
      TransportSemantics TruthReceipt NewDomainPrediction Claim ContentAddress
        Domain Version NewEvidence)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim)
    (J J' : Domain)
    (version : Version) : Prop :=
  S.strictSubset J J' /\
    S.receiptMatches cert.oldReceipt (S.claimAddress claim) J version /\
    (cert.givenPremises -> cert.transportAssumption -> S.claimOn claim J') /\
    (forall z, S.inNewOnlyDomain z J J' ->
      S.predictionDefined cert.falsifiablePrediction z) /\
    Exists fun z =>
      S.inNewOnlyDomain z J J' /\
        S.predictionDefined cert.falsifiablePrediction z /\
        S.predictionFails cert.falsifiablePrediction z /\
        S.refutes z cert claim

/-- A typed refutation extends one result-bearing failure with refutation of the
same claim by that same result. -/
structure TransportRefutationWitness
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim)
    (J J' : Domain) where
  failure : TransportFailureWitness S cert.falsifiablePrediction J J'
  refutesClaim :
    S.refutes cert.falsifiablePrediction
      failure.evidence failure.result claim

/-- The five fields are the typed proof object corresponding one-for-one to the
legacy validity clauses. -/
structure SemanticTransportCertificate
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim)
    (J J' : Domain)
    (version : Version) where
  strictExpansion : SemanticStrictSubset S J J'
  receiptBound :
    S.receiptMatches cert.oldReceipt (S.claimAddress claim) J version
  conditionalTransport :
    cert.givenPremises -> cert.transportAssumption -> S.claimOn claim J'
  totalOnNewOnly :
    forall z, SemanticNewOnly S z J J' ->
      SemanticPredictionDefined S cert.falsifiablePrediction z
  refutingFailure : TransportRefutationWitness S cert claim J J'

/-- Propositional closure of the typed semantic transport certificate. -/
def ValidSemanticTransportCert
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim)
    (J J' : Domain)
    (version : Version) : Prop :=
  Nonempty (SemanticTransportCertificate S cert claim J J' version)

/-- A typed semantic certificate is valid exactly when its unique legacy
forgetful image satisfies the original five-clause validity predicate. The
reverse direction identifies the failure and refutation results solely by
injectivity of `Option.some`; no result equality decision or uniqueness axiom
is assumed. -/
theorem valid_semantic_transport_cert_iff_valid_transport_cert
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (cert : TransportCert TruthReceipt NewDomainPrediction)
    (claim : Claim)
    (J J' : Domain)
    (version : Version) :
    ValidSemanticTransportCert S cert claim J J' version <->
      ValidTransportCert (TransportSemanticFrame.toLegacy S)
        cert claim J J' version := by
  constructor
  · rintro ⟨typed⟩
    refine ⟨typed.strictExpansion, typed.receiptBound,
      typed.conditionalTransport, typed.totalOnNewOnly, ?_⟩
    let failure := typed.refutingFailure.failure
    refine ⟨failure.evidence, failure.newOnly, ?_, ?_, ?_⟩
    · exact ⟨failure.result, failure.observed⟩
    · exact ⟨failure.result, failure.observed, failure.failed⟩
    · exact ⟨failure.result, failure.observed,
        typed.refutingFailure.refutesClaim⟩
  · rintro ⟨strictExpansion, receiptBound, conditionalTransport,
      totalOnNewOnly, z, newOnly, _defined, fails, refutes⟩
    rcases fails with ⟨failedResult, failedObserved, failedProof⟩
    rcases refutes with ⟨refutingResult, refutingObserved, refutesProof⟩
    have resultEquality : failedResult = refutingResult :=
      Option.some.inj (failedObserved.symm.trans refutingObserved)
    refine ⟨{
      strictExpansion := strictExpansion
      receiptBound := receiptBound
      conditionalTransport := conditionalTransport
      totalOnNewOnly := totalOnNewOnly
      refutingFailure := {
        failure := {
          evidence := z
          newOnly := newOnly
          result := failedResult
          observed := failedObserved
          failed := failedProof
        }
        refutesClaim := ?_
      }
    }⟩
    simpa only [resultEquality] using refutesProof

#print axioms valid_semantic_transport_cert_iff_valid_transport_cert

namespace CertificateWitness

private def frame :
    TransportSemanticFrame Unit Unit Bool Unit Bool Unit Bool Bool where
  claimAddress := fun _ => ()
  claimScope := fun _ => false
  claimVersion := fun _ => ()
  receiptMatches := fun _ _ _ _ => True
  claimOn := fun claim domain => claim = true /\ domain = true
  inDomain := fun z domain => domain = true /\ z = true
  run := fun _ z => some z
  fails := fun _ _ result => result = true
  refutes := fun _ _ result claim => result = true /\ claim = true

private def cert : TransportCert Unit Unit where
  oldReceipt := ()
  givenPremises := True
  transportAssumption := True
  falsifiablePrediction := ()

private def typedCertificate :
    SemanticTransportCertificate frame cert true false true () where
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
    refutesClaim := ⟨rfl, rfl⟩
  }

/-- Domain-inhabitance witness used by the fidelity gate. -/
example : Bool := false

/-- The theorem's typed side is satisfiable in the pinned toolchain. -/
example : ValidSemanticTransportCert frame cert true false true () :=
  ⟨typedCertificate⟩

/-- The same concrete certificate satisfies the legacy side by the public
equivalence theorem. -/
example :
    ValidTransportCert (TransportSemanticFrame.toLegacy frame)
      cert true false true () :=
  valid_semantic_transport_cert_iff_valid_transport_cert
    frame cert true false true () |>.mp ⟨typedCertificate⟩

private def undefinedFrame :
    TransportSemanticFrame Unit Unit Bool Unit Bool Unit Bool Bool :=
  { frame with run := fun _ _ => none }

/-- Negative control: a frame with no successful run cannot carry the totality
field at the concrete new-only point. -/
example :
    Not (ValidSemanticTransportCert undefinedFrame cert true false true ()) := by
  rintro ⟨typed⟩
  obtain ⟨result, observed⟩ := typed.totalOnNewOnly true (by
    simp [SemanticNewOnly, undefinedFrame, frame])
  simp [undefinedFrame] at observed

end CertificateWitness

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
