/- GID: D5/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeSemantics/FiniteTransportClauseIndependence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite table models independently falsify all five transport-certificate clauses. -/

import D5.S3.ConceptDynamics.DefinitionEscapeSemantics.SemanticTransportCertificateValidity
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.DeriveFintype

/- Library-search audit trail (2026-08-30):
   * Exact repository searches for `FiniteTransportCertificateClauseIndependence`,
     `finite_transport_certificate_clause_independence`, and indexed five-clause
     transport independence found no declaration in D5 or Blueprint.
   * Statement-shape searches for five models respectively retaining four of
     `strictExpansion`, `receiptBound`, `conditionalTransport`,
     `totalOnNewOnly`, and `refutingFailure` found only the frozen definitions
     and bridge in `SemanticTransportCertificateValidity`; no independence
     theorem or finite constrained model class was present.
   * The frozen `TransportSemanticFrame`, `TransportCert`, and
     `ValidTransportCert` are reused. The model below adds no second validity
     predicate: its indexed clauses are proved equivalent to that canonical
     five-conjunct predicate in the public theorem.
   * Pinned Mathlib supplies finite functions, `Finset`, `Fin 3`, `Fintype`, and
     native decision. No upstream theorem packages these repository-specific
     receipt, partial-prediction, failure, and refutation tables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

open D5.S3.ConceptDynamics.DefinitionEscape.Semantics

/-- A fully finite transport model. Domains are characteristic tables on three points;
premises, transport assumptions, predictions, acceptance, and claim truth are
finite tables. There are no freely assignable `Prop` fields in the model data. -/
structure FiniteTransportModel where
  oldDomain : Fin 3 → Bool
  reportedDomain : Fin 3 → Bool
  claim : Bool
  version : Bool
  receipt : Bool × (Fin 3 → Bool) × Bool
  premiseTable : Fin 1 → Bool
  transportTable : Fin 1 → Bool
  predictionTable : Fin 3 → Option Bool
  acceptanceTable : Fin 3 → Bool → Bool
  truthTable : Bool → Fin 3 → Bool
deriving DecidableEq

/-- The five top-level coordinates of the canonical transport-certificate
validity predicate, in their DECT 54.3 order. -/
inductive TransportCertificateClause
  | strictExpansion
  | receiptBound
  | conditionalTransport
  | totalOnNewOnly
  | refutingFailure
deriving DecidableEq, Fintype

/-- The canonical certificate carrier populated only from the two finite
Boolean premise tables and the finite partial-prediction table. -/
def finiteTransportCertificate
    (model : FiniteTransportModel) :
    TransportCert
      (Bool × (Fin 3 → Bool) × Bool) (Fin 3 → Option Bool) where
  oldReceipt := model.receipt
  givenPremises := model.premiseTable 0 = true
  transportAssumption := model.transportTable 0 = true
  falsifiablePrediction := model.predictionTable

/-- The result-bearing semantic frame forced by a finite model. Membership is
`Finset` membership, receipts match exactly in all three fields, definedness is
the graph domain of the partial table, failure is rejection of an observed
value, and refutation is disagreement with the same claim-truth table used by
`claimOn`. -/
def finiteTransportFrame
    (model : FiniteTransportModel) :
    TransportSemanticFrame
      (Bool × (Fin 3 → Bool) × Bool) (Fin 3 → Option Bool) Bool Bool
      (Fin 3 → Bool) Bool (Fin 3) Bool where
  claimAddress := id
  claimScope := fun _ => model.oldDomain
  claimVersion := fun _ => model.version
  receiptMatches := fun receipt address domain version =>
    receipt.1 = address ∧ receipt.2.1 = domain ∧ receipt.2.2 = version
  claimOn := fun claim domain =>
    ∀ point, domain point = true → model.truthTable claim point = true
  inDomain := fun point domain => domain point = true
  run := fun prediction point => prediction point
  fails := fun _ point result => model.acceptanceTable point result = false
  refutes := fun _ point result claim => result ≠ model.truthTable claim point

/-- One indexed coordinate of the canonical five-conjunct validity predicate,
read through the unique legacy image of the finite result-bearing frame. -/
def finiteTransportClauseHolds
    (model : FiniteTransportModel)
    (clause : TransportCertificateClause) : Prop :=
  let semantics := TransportSemanticFrame.toLegacy (finiteTransportFrame model)
  let certificate := finiteTransportCertificate model
  match clause with
  | .strictExpansion =>
      semantics.strictSubset model.oldDomain model.reportedDomain
  | .receiptBound =>
      semantics.receiptMatches certificate.oldReceipt
        (semantics.claimAddress model.claim) model.oldDomain model.version
  | .conditionalTransport =>
      certificate.givenPremises → certificate.transportAssumption →
        semantics.claimOn model.claim model.reportedDomain
  | .totalOnNewOnly =>
      ∀ point, semantics.inNewOnlyDomain point
          model.oldDomain model.reportedDomain →
        semantics.predictionDefined certificate.falsifiablePrediction point
  | .refutingFailure =>
      ∃ point,
        semantics.inNewOnlyDomain point model.oldDomain model.reportedDomain ∧
        semantics.predictionDefined certificate.falsifiablePrediction point ∧
        semantics.predictionFails certificate.falsifiablePrediction point ∧
        semantics.refutes point certificate model.claim

instance finiteTransportClauseHoldsDecidable
    (model : FiniteTransportModel) (clause : TransportCertificateClause) :
    Decidable (finiteTransportClauseHolds model clause) := by
  cases clause <;>
    simp only [finiteTransportClauseHolds, finiteTransportCertificate,
      finiteTransportFrame, TransportSemanticFrame.toLegacy,
      SemanticStrictSubset, SemanticNewOnly, SemanticPredictionDefined,
      SemanticPredictionFails, SemanticRefutes] <;>
    infer_instance

/-- The concrete bad-report observation paired with each deleted coordinate.
Each case reads finite data directly rather than defining badness as the
negation of `finiteTransportClauseHolds`. -/
def finiteTransportBadReport
    (model : FiniteTransportModel)
    (clause : TransportCertificateClause) : Prop :=
  match clause with
  | .strictExpansion =>
      ∃ point,
        model.oldDomain point = true ∧ model.reportedDomain point = false
  | .receiptBound =>
      model.receipt.1 ≠ model.claim ∨
        model.receipt.2.1 ≠ model.oldDomain ∨
        model.receipt.2.2 ≠ model.version
  | .conditionalTransport =>
      model.premiseTable 0 = true ∧
        model.transportTable 0 = true ∧
        ∃ point, model.reportedDomain point = true ∧
          model.truthTable model.claim point = false
  | .totalOnNewOnly =>
      ∃ point,
        model.reportedDomain point = true ∧ model.oldDomain point = false ∧
          model.predictionTable point = none
  | .refutingFailure =>
      ∀ point, model.reportedDomain point = true →
        model.oldDomain point = false →
        ∀ result, model.predictionTable point = some result →
          model.acceptanceTable point result = true ∨
            result = model.truthTable model.claim point

instance finiteTransportBadReportDecidable
    (model : FiniteTransportModel) (clause : TransportCertificateClause) :
    Decidable (finiteTransportBadReport model clause) := by
  cases clause <;> simp only [finiteTransportBadReport] <;> infer_instance

private def strictExpansionCountermodel : FiniteTransportModel where
  oldDomain := fun point => point == 0 || point == 2
  reportedDomain := fun point => point == 1 || point == 2
  claim := false
  version := false
  receipt := (false, fun point => point == 0 || point == 2, false)
  premiseTable := fun _ => true
  transportTable := fun _ => true
  predictionTable := fun point => if point = 1 then some false else none
  acceptanceTable := fun _ _ => false
  truthTable := fun _ _ => true

private def receiptCountermodel : FiniteTransportModel where
  oldDomain := fun point => point == 0
  reportedDomain := fun point => point == 0 || point == 1
  claim := false
  version := false
  receipt := (true, fun point => point == 0, false)
  premiseTable := fun _ => true
  transportTable := fun _ => true
  predictionTable := fun point => if point = 1 then some false else none
  acceptanceTable := fun _ _ => false
  truthTable := fun _ _ => true

private def conditionalTransportCountermodel : FiniteTransportModel where
  oldDomain := fun point => point == 0
  reportedDomain := fun point => point == 0 || point == 1
  claim := false
  version := false
  receipt := (false, fun point => point == 0, false)
  premiseTable := fun _ => true
  transportTable := fun _ => true
  predictionTable := fun point => if point = 1 then some true else none
  acceptanceTable := fun _ _ => false
  truthTable := fun _ point => point ≠ 1

private def totalityCountermodel : FiniteTransportModel where
  oldDomain := fun point => point == 0
  reportedDomain := fun _ => true
  claim := false
  version := false
  receipt := (false, fun point => point == 0, false)
  premiseTable := fun _ => true
  transportTable := fun _ => true
  predictionTable := fun point => if point = 2 then some false else none
  acceptanceTable := fun _ _ => false
  truthTable := fun _ _ => true

private def refutingFailureCountermodel : FiniteTransportModel where
  oldDomain := fun point => point == 0
  reportedDomain := fun point => point == 0 || point == 1
  claim := false
  version := false
  receipt := (false, fun point => point == 0, false)
  premiseTable := fun _ => true
  transportTable := fun _ => true
  predictionTable := fun point => if point = 1 then some true else none
  acceptanceTable := fun _ _ => true
  truthTable := fun _ _ => true

/-- The indexed finite clauses first recombine exactly to the frozen canonical
`ValidTransportCert`. Moreover, for each coordinate there is an enumerable
three-point table model in which every other coordinate holds, that coordinate
fails, and its independently read bad-report observation holds. -/
theorem finite_transport_certificate_clause_independence :
    (∀ model : FiniteTransportModel,
      (∀ clause, finiteTransportClauseHolds model clause) ↔
        ValidTransportCert
          (TransportSemanticFrame.toLegacy (finiteTransportFrame model))
          (finiteTransportCertificate model) model.claim
          model.oldDomain model.reportedDomain model.version) ∧
    ∀ omitted : TransportCertificateClause,
      ∃ model : FiniteTransportModel,
        (∀ retained, retained ≠ omitted →
          finiteTransportClauseHolds model retained) ∧
        ¬ finiteTransportClauseHolds model omitted ∧
        finiteTransportBadReport model omitted := by
  constructor
  · intro model
    constructor
    · intro clauses
      exact ⟨clauses .strictExpansion, clauses .receiptBound,
        clauses .conditionalTransport, clauses .totalOnNewOnly,
        clauses .refutingFailure⟩
    · rintro ⟨strictExpansion, receiptBound, conditionalTransport,
        totalOnNewOnly, refutingFailure⟩ clause
      cases clause with
      | strictExpansion => exact strictExpansion
      | receiptBound => exact receiptBound
      | conditionalTransport => exact conditionalTransport
      | totalOnNewOnly => exact totalOnNewOnly
      | refutingFailure => exact refutingFailure
  · intro omitted
    cases omitted with
    | strictExpansion =>
        exact ⟨strictExpansionCountermodel, by decide⟩
    | receiptBound =>
        exact ⟨receiptCountermodel, by decide⟩
    | conditionalTransport =>
        exact ⟨conditionalTransportCountermodel, by decide⟩
    | totalOnNewOnly =>
        exact ⟨totalityCountermodel, by decide⟩
    | refutingFailure =>
        exact ⟨refutingFailureCountermodel, by decide⟩

#print axioms finite_transport_certificate_clause_independence

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
