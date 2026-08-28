/- GID: D5/S3/ConceptDynamics/DefinitionEscapeSemantics/TransportRefutationProjection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeSemantics/TransportRefutationProjection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A typed refutation witness projects to same-run semantic propositions. -/

/- Library-search audit trail (2026-08-29):
   * Exact repository search for `TransportRefutationWitness`,
     `TransportFailureWitness`, `SemanticPredictionDefined`,
     `SemanticPredictionFails`, and `SemanticRefutes` found no declaration.
   * Statement-shape searches for a new-domain witness carrying a concrete
     prediction result, failure, and claim-bound refutation found only the
     frozen Prop-level `TransportCertificateValidity` predicates. Those are
     reused through their `TransportCert` and `FalsifiablePrediction` carriers.
   * The frozen `SemanticStrictSubsetWitness` module supplies
     `TransportSemanticFrame` and `SemanticNewOnly`; both are imported rather
     than restated. No result-equality or decidability theorem is needed.
   * Pinned Mathlib exact-name and statement-shape searches for these five
     declarations and for a partial-run failure/refutation projection returned
     no hit; the claim is repository-specific structure projection. -/

import D5.S3.ConceptDynamics.DefinitionEscapeSemantics.SemanticStrictSubsetWitness
import D5.S3.ConceptDynamics.Transport.TransportCertificateValidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Semantics

open D5.S3.ConceptDynamics.Transport.TransportCertificateValidity

universe u v

/-- A semantic prediction is defined at a point exactly when its partial run
returns a concrete result there. -/
def SemanticPredictionDefined
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (prediction : NewDomainPrediction)
    (z : NewEvidence) : Prop :=
  Exists fun result => S.run prediction z = some result

/-- A semantic prediction fails at a point only through a result returned by
the partial run at that same point. -/
def SemanticPredictionFails
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (prediction : NewDomainPrediction)
    (z : NewEvidence) : Prop :=
  Exists fun result =>
    S.run prediction z = some result /\
      S.fails prediction z result

/-- Refutation projects the registered prediction from the canonical transport
certificate and binds it to a result returned at the supplied evidence point. -/
def SemanticRefutes
    {Point Payload Claim ContentAddress Version Error : Type u}
    {PredictionResult : Type v}
    {source target : Set Point}
    (S :
      TransportSemanticFrame
        (Receipt Point Payload ContentAddress Version Error)
        (FalsifiablePrediction Point Claim source target)
        Claim ContentAddress (Set Point) Version Point PredictionResult)
    (z : Point)
    (cert :
      TransportCert Point Payload Claim ContentAddress Version Error
        source target)
    (claim : Claim) : Prop :=
  Exists fun result =>
    S.run cert.falsifiablePrediction z = some result /\
      S.refutes cert.falsifiablePrediction z result claim

/-- A failure witness stores one new-domain point and one concrete result that
was both returned and classified as a failure at that point. -/
structure TransportFailureWitness
    {TruthReceipt NewDomainPrediction Claim ContentAddress Domain Version
      NewEvidence : Type u}
    {PredictionResult : Type v}
    (S :
      TransportSemanticFrame TruthReceipt NewDomainPrediction Claim
        ContentAddress Domain Version NewEvidence PredictionResult)
    (prediction : NewDomainPrediction)
    (J J' : Domain) where
  evidence : NewEvidence
  newOnly : SemanticNewOnly S evidence J J'
  result : PredictionResult
  observed : S.run prediction evidence = some result
  failed : S.fails prediction evidence result

/-- A refutation witness extends one typed failure of the prediction registered
by the canonical transport certificate with a refutation of the same claim. -/
structure TransportRefutationWitness
    {Point Payload Claim ContentAddress Version Error : Type u}
    {PredictionResult : Type v}
    {source target : Set Point}
    (S :
      TransportSemanticFrame
        (Receipt Point Payload ContentAddress Version Error)
        (FalsifiablePrediction Point Claim source target)
        Claim ContentAddress (Set Point) Version Point PredictionResult)
    (cert :
      TransportCert Point Payload Claim ContentAddress Version Error
        source target)
    (claim : Claim)
    (J J' : Set Point) where
  failure :
    TransportFailureWitness S cert.falsifiablePrediction J J'
  refutesClaim :
    S.refutes cert.falsifiablePrediction
      failure.evidence failure.result claim

/-- A typed refutation witness projects to the four public propositions at one
evidence point. All three run-dependent propositions use the result stored in
the witness rather than independently chosen results. -/
theorem transport_refutation_witness_projects_to_prop
    {Point Payload Claim ContentAddress Version Error : Type u}
    {PredictionResult : Type v}
    {source target J J' : Set Point}
    (S :
      TransportSemanticFrame
        (Receipt Point Payload ContentAddress Version Error)
        (FalsifiablePrediction Point Claim source target)
        Claim ContentAddress (Set Point) Version Point PredictionResult)
    (cert :
      TransportCert Point Payload Claim ContentAddress Version Error
        source target)
    (claim : Claim)
    (w : TransportRefutationWitness S cert claim J J') :
    Exists fun z =>
      SemanticNewOnly S z J J' /\
        SemanticPredictionDefined S cert.falsifiablePrediction z /\
        SemanticPredictionFails S cert.falsifiablePrediction z /\
        SemanticRefutes S z cert claim := by
  refine ⟨w.failure.evidence, w.failure.newOnly, ?_, ?_, ?_⟩
  · exact ⟨w.failure.result, w.failure.observed⟩
  · exact ⟨w.failure.result, w.failure.observed, w.failure.failed⟩
  · exact ⟨w.failure.result, w.failure.observed, w.refutesClaim⟩

namespace RefutationWitnessExample

/-- The frozen Boolean certificate receives a result-bearing interpretation
without changing its registered prediction. -/
private def booleanTransportFrame :
    TransportSemanticFrame
      (Receipt Bool Unit Nat Nat Nat)
      (FalsifiablePrediction Bool Bool FiniteWitness.source
        FiniteWitness.target)
      Bool Nat (Set Bool) Nat Bool Bool where
  claimAddress := FiniteWitness.semantics.claimAddress
  claimScope := fun _ => FiniteWitness.source
  claimVersion := FiniteWitness.semantics.version
  receiptMatches := fun receipt address domain version =>
    ReceiptMatches receipt FiniteWitness.record address domain version
  claimOn := FiniteWitness.semantics.claimOn
  inDomain := fun z domain => domain z
  run := fun _ z => some z
  fails := fun prediction z result => prediction.failsAt z /\ result = z
  refutes := fun prediction z result claim =>
    prediction.refutes z claim /\ result = z

private def booleanRefutationWitness :
    TransportRefutationWitness booleanTransportFrame
      FiniteWitness.certificate true
      FiniteWitness.source FiniteWitness.target where
  failure := {
    evidence := true
    newOnly := by
      change true ∈ FiniteWitness.target \ FiniteWitness.source
      exact FiniteWitness.true_mem_target_difference
    result := true
    observed := rfl
    failed := by
      simp [booleanTransportFrame, FiniteWitness.certificate,
        FiniteWitness.prediction]
  }
  refutesClaim := by
    simp [booleanTransportFrame, FiniteWitness.certificate,
      FiniteWitness.prediction]

/-- The public witness hypothesis is inhabited by the frozen Boolean transport
certificate and a concrete same-run refutation. -/
example :
    Nonempty
      (TransportRefutationWitness booleanTransportFrame
        FiniteWitness.certificate true
        FiniteWitness.source FiniteWitness.target) :=
  Nonempty.intro booleanRefutationWitness

/-- The theorem projects the concrete witness without replacing its point or
its returned Boolean result. -/
example :
    Exists fun z =>
      SemanticNewOnly booleanTransportFrame z
          FiniteWitness.source FiniteWitness.target /\
        SemanticPredictionDefined booleanTransportFrame
          FiniteWitness.certificate.falsifiablePrediction z /\
        SemanticPredictionFails booleanTransportFrame
          FiniteWitness.certificate.falsifiablePrediction z /\
        SemanticRefutes booleanTransportFrame z
          FiniteWitness.certificate true :=
  transport_refutation_witness_projects_to_prop
    booleanTransportFrame FiniteWitness.certificate true
    booleanRefutationWitness

private def undefinedTransportFrame :
    TransportSemanticFrame
      (Receipt Bool Unit Nat Nat Nat)
      (FalsifiablePrediction Bool Bool FiniteWitness.source
        FiniteWitness.target)
      Bool Nat (Set Bool) Nat Bool Bool :=
  { booleanTransportFrame with run := fun _ _ => none }

/-- Negative control: if every run is undefined, even the definedness conjunct
of the projected conclusion is impossible. -/
example :
    Not (Exists fun z =>
      SemanticNewOnly undefinedTransportFrame z
          FiniteWitness.source FiniteWitness.target /\
        SemanticPredictionDefined undefinedTransportFrame
          FiniteWitness.certificate.falsifiablePrediction z /\
        SemanticPredictionFails undefinedTransportFrame
          FiniteWitness.certificate.falsifiablePrediction z /\
        SemanticRefutes undefinedTransportFrame z
          FiniteWitness.certificate true) := by
  rintro ⟨z, _newOnly, defined, _fails, _refutes⟩
  rcases defined with ⟨result, observed⟩
  simp [undefinedTransportFrame] at observed

end RefutationWitnessExample

#print axioms transport_refutation_witness_projects_to_prop

end D5.S3.ConceptDynamics.DefinitionEscape.Semantics
