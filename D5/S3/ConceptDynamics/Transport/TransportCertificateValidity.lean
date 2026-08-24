/- GID: D5/S3/ConceptDynamics/Transport/TransportCertificateValidity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/TransportCertificateValidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Valid transport certificates need locked receipts and nonempty failures. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-24):
   * Exact repository search
     `rg -n 'TransportCert|ValidTransport|HasValidTransport|ReceiptMatches|TruthRecord|
     ClaimAddress|ClaimOn|PredictionDefined|PredictionFails|FalsifiablePrediction|
     TransportAssumption|GivenPremises|Refutes' D5 Blueprint` returned no matches.
   * Type-shape searches
     `rg -n '^structure .*Certificate|^structure .*Receipt|^structure .*Prediction|
     ^structure .*Assumption|^def .*Valid.*: Prop|^def .*Set .*Set.*: Prop'
     D5/S3/ConceptDynamics` found only the unrelated `ValidAgenda`; the broader
     `Set (...)`, `Set _ -> Prop`, and quantified-membership search found relation
     kernels, hitting sets, and `Set.Nonempty` uses, but no claim-bound certificate.
   * English synonym searches for transport/extrapolation/generalization,
     certificate/receipt/record, prediction/falsification/failure/refutation,
     assumption/premise/invariance/stability, and selection/intervention/covariate/loss
     found only neighboring transport, prediction, and stability theorems. None stores
     a source record or packages the four validity clauses. The corresponding Chinese
     searches for `运输|外推|迁移|范围|定义域|新域`, `收据|凭证|证书|记录|内容地址|
     主张|版本`, `预测|可证伪|可失败|失败事件|反驳|预登记`, and
     `假设|前提|不变|稳定|选择机制|干预一致|协变量|损失稳定` returned no matches.
   * Neighbor audit `ls D5/S3/ConceptDynamics/Transport/` and
     `git grep -n '^def \|^  def ' -- D5/S3/ConceptDynamics | head -60` found
     function transport, descent, and validity-preservation modules, but no receipt,
     certificate, scoped claim, or falsifiable-prediction vocabulary to reuse.
   * Pinned-Mathlib exact-name search returned no domain hit. Its `Set.Nonempty`
     predicate is the existing shape used below; `loogle` and `leansearch` are absent
     from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.TransportCertificateValidity

/-- A truth record retains its payload together with the scope, version, error,
and transported claim address under which that payload was recorded. -/
structure TruthRecord
    (Point Payload Address Version Error : Type*) where
  payload : Payload
  domain : Set Point
  version : Version
  error : Error
  claimAddress : Address

/-- A receipt stores the original record and seals all of its transport-relevant
coordinates. In particular, the error cannot be changed independently of the
stored record. -/
structure Receipt
    (Point Payload Address Version Error : Type*) where
  originalRecord : TruthRecord Point Payload Address Version Error
  sourceDomain : Set Point
  sourceVersion : Version
  sourceError : Error
  transportedClaimAddress : Address
  locksOriginal :
    originalRecord.domain = sourceDomain ∧
      originalRecord.version = sourceVersion ∧
      originalRecord.error = sourceError ∧
      originalRecord.claimAddress = transportedClaimAddress

/-- The public interpretation of a claim's content address, version, and scope. -/
structure ClaimSemantics (Point Claim Address Version : Type*) where
  claimAddress : Claim → Address
  version : Claim → Version
  claimOn : Claim → Set Point → Prop

/-- Truth records indexed by the source scope and declared error. -/
def TruthRecordAt
    {Point Payload Address Version Error : Type*}
    (source : Set Point) (error : Error) :=
  {record : TruthRecord Point Payload Address Version Error //
    record.domain = source ∧ record.error = error}

/-- Claims indexed by the scope on which they hold. -/
def ClaimAt
    {Point Claim Address Version : Type*}
    (semantics : ClaimSemantics Point Claim Address Version)
    (target : Set Point) :=
  {claim : Claim // semantics.claimOn claim target}

/-- A scope-transport candidate maps a source-scoped, error-indexed truth record
to a claim that is already scoped to the target domain. -/
def ScopeTransportCandidate
    {Point Payload Claim Address Version Error : Type*}
    (semantics : ClaimSemantics Point Claim Address Version)
    (source target : Set Point) (error : Error) :=
  TruthRecordAt (Payload := Payload) (Address := Address) (Version := Version)
      source error →
    ClaimAt semantics target

/-- Every optional dependency is named inside the assumption object. If transport
uses selection, intervention consistency, covariate transformation, or loss
stability, validity requires the corresponding invariant rather than hiding it
under an informal similarity premise. -/
structure TransportAssumption where
  givenPremises : Prop
  preservedStructures : Prop
  usesSelectionMechanism : Prop
  selectionMechanismPreserved : Prop
  usesInterventionConsistency : Prop
  interventionConsistencyPreserved : Prop
  usesCovariateTransformation : Prop
  covariateTransformationPreserved : Prop
  usesLossStability : Prop
  lossStabilityPreserved : Prop

/-- The explicit preservation obligations carried by a transport assumption. -/
def TransportAssumption.Holds (assumption : TransportAssumption) : Prop :=
  assumption.preservedStructures ∧
    (assumption.usesSelectionMechanism →
      assumption.selectionMechanismPreserved) ∧
    (assumption.usesInterventionConsistency →
      assumption.interventionConsistencyPreserved) ∧
    (assumption.usesCovariateTransformation →
      assumption.covariateTransformationPreserved) ∧
    (assumption.usesLossStability → assumption.lossStabilityPreserved)

/-- A falsifiable prediction carries a preregistered definition predicate, a
failure predicate, and a claim-bound refutation predicate. Its type requires a
nonempty failure event inside the new-domain difference. -/
structure FalsifiablePrediction
    (Point Claim : Type*) (source target : Set Point) where
  definedAt : Point → Prop
  failsAt : Point → Prop
  refutes : Point → Claim → Prop
  nonemptyFailure :
    ∃ z, z ∈ target \ source ∧ definedAt z ∧ failsAt z

/-- The minimum transport-certificate data: source receipt, explicit transport
assumption, and falsifiable target-difference prediction. -/
structure TransportCert
    (Point Payload Claim Address Version Error : Type*)
    (source target : Set Point) where
  receipt : Receipt Point Payload Address Version Error
  transportAssumption : TransportAssumption
  falsifiablePrediction : FalsifiablePrediction Point Claim source target

def ClaimAddress
    {Point Claim Address Version : Type*}
    (semantics : ClaimSemantics Point Claim Address Version)
    (claim : Claim) : Address :=
  semantics.claimAddress claim

def Version
    {Point Claim Address Version : Type*}
    (semantics : ClaimSemantics Point Claim Address Version)
    (claim : Claim) : Version :=
  semantics.version claim

def ClaimOn
    {Point Claim Address Version : Type*}
    (semantics : ClaimSemantics Point Claim Address Version)
    (claim : Claim) (domain : Set Point) : Prop :=
  semantics.claimOn claim domain

def ReceiptMatches
    {Point Payload Address Version Error : Type*}
    (receipt : Receipt Point Payload Address Version Error)
    (address : Address) (source : Set Point) (version : Version) : Prop :=
  receipt.sourceDomain = source ∧
    receipt.sourceVersion = version ∧
    receipt.transportedClaimAddress = address

def GivenPremises
    {Point Payload Claim Address Version Error : Type*}
    {source target : Set Point}
    (certificate :
      TransportCert Point Payload Claim Address Version Error source target) : Prop :=
  certificate.transportAssumption.givenPremises

def PredictionDefined
    {Point Payload Claim Address Version Error : Type*}
    {source target : Set Point}
    (certificate :
      TransportCert Point Payload Claim Address Version Error source target)
    (z : Point) : Prop :=
  certificate.falsifiablePrediction.definedAt z

def PredictionFails
    {Point Payload Claim Address Version Error : Type*}
    {source target : Set Point}
    (certificate :
      TransportCert Point Payload Claim Address Version Error source target)
    (z : Point) : Prop :=
  certificate.falsifiablePrediction.failsAt z

def Refutes
    {Point Payload Claim Address Version Error : Type*}
    {source target : Set Point}
    (z : Point)
    (certificate :
      TransportCert Point Payload Claim Address Version Error source target)
    (claim : Claim) : Prop :=
  certificate.falsifiablePrediction.refutes z claim

/-- A transport certificate is valid exactly when its receipt matches the claim,
its explicit premises and assumptions conditionally transport the claim, its
prediction covers the whole target difference, and one preregistered failure
witness refutes that same claim. -/
def ValidTransportCert
    {Point Payload Claim Address Version Error : Type*}
    {source target : Set Point}
    (semantics : ClaimSemantics Point Claim Address Version)
    (certificate :
      TransportCert Point Payload Claim Address Version Error source target)
    (claim : Claim) (version : Version) : Prop :=
  ReceiptMatches certificate.receipt (ClaimAddress semantics claim) source version ∧
    ((GivenPremises certificate ∧ certificate.transportAssumption.Holds) →
      ClaimOn semantics claim target) ∧
    (∀ z ∈ target \ source, PredictionDefined certificate z) ∧
    ∃ z, z ∈ target \ source ∧
      PredictionDefined certificate z ∧
      PredictionFails certificate z ∧
      Refutes z certificate claim

/-- Existence is closed over the same claim-bound validity predicate and fixes
the certificate version to the claim's own version. -/
def HasValidTransportCert
    {Point Payload Claim Address ClaimVersion Error : Type*}
    (semantics : ClaimSemantics Point Claim Address ClaimVersion)
    (claim : Claim) (source target : Set Point) : Prop :=
  ∃ certificate :
      TransportCert Point Payload Claim Address ClaimVersion Error source target,
    ValidTransportCert semantics certificate claim (Version semantics claim)

/-- Receipt matching exposes the source coordinates sealed against the original
record, including its error and transported claim address. -/
theorem receipt_matches_original_coordinates
    {Point Payload Address Version Error : Type*}
    {source : Set Point} {address : Address} {version : Version}
    (receipt : Receipt Point Payload Address Version Error)
    (receiptMatch : ReceiptMatches receipt address source version) :
    receipt.originalRecord.domain = source ∧
      receipt.originalRecord.version = version ∧
      receipt.originalRecord.error = receipt.sourceError ∧
      receipt.originalRecord.claimAddress = address := by
  rcases receipt.locksOriginal with ⟨domainLock, versionLock, errorLock, addressLock⟩
  rcases receiptMatch with ⟨domainMatch, versionMatch, addressMatch⟩
  exact ⟨domainLock.trans domainMatch, versionLock.trans versionMatch,
    errorLock, addressLock.trans addressMatch⟩

/-- The public packed criterion contains every conjunct of certificate validity. -/
theorem valid_transport_cert_criterion
    {Point Payload Claim Address Version Error : Type*}
    {source target : Set Point}
    (semantics : ClaimSemantics Point Claim Address Version)
    (certificate :
      TransportCert Point Payload Claim Address Version Error source target)
    (claim : Claim) (version : Version) :
    ValidTransportCert semantics certificate claim version ↔
      ReceiptMatches certificate.receipt (ClaimAddress semantics claim) source version ∧
      ((GivenPremises certificate ∧ certificate.transportAssumption.Holds) →
        ClaimOn semantics claim target) ∧
      (∀ z ∈ target \ source, PredictionDefined certificate z) ∧
      ∃ z, z ∈ target \ source ∧
        PredictionDefined certificate z ∧
        PredictionFails certificate z ∧
        Refutes z certificate claim :=
  Iff.rfl

/-- Failure of any one of the four public conjuncts invalidates the certificate. -/
theorem valid_transport_cert_fails_if_any_clause_fails
    {Point Payload Claim Address Version Error : Type*}
    {source target : Set Point}
    (semantics : ClaimSemantics Point Claim Address Version)
    (certificate :
      TransportCert Point Payload Claim Address Version Error source target)
    (claim : Claim) (version : Version)
    (failure :
      ¬ReceiptMatches certificate.receipt (ClaimAddress semantics claim) source version ∨
      ¬((GivenPremises certificate ∧ certificate.transportAssumption.Holds) →
        ClaimOn semantics claim target) ∨
      ¬(∀ z ∈ target \ source, PredictionDefined certificate z) ∨
      ¬(∃ z, z ∈ target \ source ∧
        PredictionDefined certificate z ∧
        PredictionFails certificate z ∧
        Refutes z certificate claim)) :
    ¬ValidTransportCert semantics certificate claim version := by
  rintro ⟨receiptMatch, conditionalTransport, definitionCoverage, refutingFailure⟩
  rcases failure with receiptFailure | conditionalFailure | coverageFailure | witnessFailure
  · exact receiptFailure receiptMatch
  · exact conditionalFailure conditionalTransport
  · exact coverageFailure definitionCoverage
  · exact witnessFailure refutingFailure

/-- The type-level nondegeneracy field rules out a constantly false failure
predicate before certificate validity is even considered. -/
theorem falsifiable_prediction_failure_is_not_const_false
    {Point Claim : Type*} {source target : Set Point}
    (prediction : FalsifiablePrediction Point Claim source target) :
    prediction.failsAt ≠ fun _ => False := by
  intro constantlyFalse
  obtain ⟨z, _newDomain, _defined, fails⟩ := prediction.nonemptyFailure
  rw [constantlyFalse] at fails
  exact fails

namespace FiniteWitness

def source : Set Bool := {false}

def target : Set Bool := Set.univ

theorem true_mem_target_difference : true ∈ target \ source := by
  change True ∧ true ≠ false
  constructor
  · trivial
  · intro equality
    cases equality

def record : TruthRecord Bool Unit Nat Nat Nat where
  payload := ()
  domain := source
  version := 7
  error := 3
  claimAddress := 11

def receipt : Receipt Bool Unit Nat Nat Nat where
  originalRecord := record
  sourceDomain := source
  sourceVersion := 7
  sourceError := 3
  transportedClaimAddress := 11
  locksOriginal := by simp [record]

def semantics : ClaimSemantics Bool Bool Nat Nat where
  claimAddress claim := if claim then 11 else 12
  version _claim := 7
  claimOn claim domain := claim = true ∧ domain = target

def assumption : TransportAssumption where
  givenPremises := True
  preservedStructures := True
  usesSelectionMechanism := True
  selectionMechanismPreserved := True
  usesInterventionConsistency := True
  interventionConsistencyPreserved := True
  usesCovariateTransformation := True
  covariateTransformationPreserved := True
  usesLossStability := True
  lossStabilityPreserved := True

def prediction : FalsifiablePrediction Bool Bool source target where
  definedAt z := z = true
  failsAt z := z = true
  refutes z claim := z = true ∧ claim = true
  nonemptyFailure := by
    exact ⟨true, true_mem_target_difference, rfl, rfl⟩

def certificate : TransportCert Bool Unit Bool Nat Nat Nat source target where
  receipt := receipt
  transportAssumption := assumption
  falsifiablePrediction := prediction

/-- Positive control: the target difference is nonempty and its concrete failure
witness both fails and refutes the transported Boolean claim. -/
example :
    ValidTransportCert semantics certificate true 7 ∧
      true ∈ target \ source ∧
      PredictionDefined certificate true ∧
      PredictionFails certificate true ∧
      Refutes true certificate true := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp [ReceiptMatches, ClaimAddress, semantics, certificate, receipt]
    · simp [GivenPremises, TransportAssumption.Holds, ClaimOn, semantics,
        certificate, assumption, target]
    · intro z hz
      change z ∈ Set.univ ∧ z ∉ ({false} : Set Bool) at hz
      cases z
      · exact (hz.2 (by rfl)).elim
      · rfl
    · refine ⟨true, ?_, ?_, ?_, ?_⟩
      · exact true_mem_target_difference
      · rfl
      · rfl
      · exact ⟨rfl, rfl⟩
  · exact ⟨true_mem_target_difference, rfl, rfl, ⟨rfl, rfl⟩⟩

/-- Negative control: full preregistration alone permits a constantly false raw
failure predicate, so the nonempty-failure field cannot be dropped from the type. -/
example :
    let definedAt : Bool → Prop := fun _ => True
    let failsAt : Bool → Prop := fun _ => False
    (∀ z ∈ target \ source, definedAt z) ∧
      ¬∃ z, z ∈ target \ source ∧ definedAt z ∧ failsAt z := by
  simp

/-- The finite target difference admits no typed constantly-false prediction. -/
example :
    ¬∃ candidate : FalsifiablePrediction Bool Bool source target,
      candidate.failsAt = fun _ => False := by
  rintro ⟨candidate, constantlyFalse⟩
  exact falsifiable_prediction_failure_is_not_const_false candidate constantlyFalse

end FiniteWitness

#print axioms valid_transport_cert_criterion
#print axioms valid_transport_cert_fails_if_any_clause_fails
#print axioms falsifiable_prediction_failure_is_not_const_false

end D5.S3.ConceptDynamics.Transport.TransportCertificateValidity
