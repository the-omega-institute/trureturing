/- GID: D5/S3/ConceptDynamics/Transport/OverreachWithoutLicense
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/OverreachWithoutLicense
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Licensed reports retain transport conditions and expansion reopens completion. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
import D5.S3.ConceptDynamics.Transport.TransportCertificateValidity
import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-08-24):
   * Type-shape search found the canonical `TransportCert`, `TruthRecord`,
     `ClaimSemantics`, and `ValidTransportCert` declarations in the neighboring
     `TransportCertificateValidity` module. They are imported and reused here;
     this module defines no second certificate-validity predicate.
   * English synonym search
     `rg -n --glob '*.lean' 'overreach|unauthorized|unlicensed|license|scope|
     domain.*(extend|expan)|reopen|closure|completion' D5/S3/ConceptDynamics`
     found `AdmissionValidityPreservation`, `PrecedentTargetCompletion`, and
     `TargetClosureOperator`. The first transports predicate validity, the
     second uses old-case agreement, and the third closes a concept under a
     target readout; none licenses a claimed larger operation scope.
   * Chinese synonym search
     `rg -n '越权|授权|许可证|许可|扩域|重新打开|重开|闭合|完成|运输|
     报告|前件|假设' D5 Blueprint` found no content declaration in
     this family (only unrelated governance prose outside ConceptDynamics).
   * Neighbor-vocabulary search
     `ls D5/S3/ConceptDynamics/Transport D5/S3/ConceptDynamics/Completion
     D5/S3/ConceptDynamics/DefinitionEscape` and
     `git grep -n -E '^def |^  def ' -- D5/S3/ConceptDynamics | head -60`
     found no license or overreach definition. Exact hits `Concept`, the
     transport-certificate declarations, and the canonical `defectRelation`
     are imported and reused. Scope restriction changes only its state type;
     this module introduces no second residual or closure predicate.
   * Pinned-Mathlib shape search
     `rg -n 'theorem ssubset_iff_exists|ssubset_iff_exists'
     .lake/packages/mathlib/Mathlib/Data/Set .lake/packages/mathlib/Mathlib`
     found `Set.ssubset_iff_exists`; it is used directly for concrete strict
     scope-expansion witnesses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.OverreachWithoutLicense

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Transport.TransportCertificateValidity

/-- A transport report contains the transported concept, the scope it claims,
and the condition retained in the report. -/
structure TransportReport (Operation State Coordinate : Type*) where
  concept : Concept State Coordinate
  reportedScope : Set Operation
  condition : Prop

/-- A report is licensed exactly when a certificate satisfying the canonical
transport-validity definition retains its full premises and explicit
preservation obligations as the report condition. -/
def LicensedReport
    {Operation State Coordinate Payload Address ClaimVersion Error : Type*}
    (semantics :
      ClaimSemantics Operation (Concept State Coordinate) Address ClaimVersion)
    (record : TruthRecord Operation Payload Address ClaimVersion Error)
    (q : TransportReport Operation State Coordinate)
    (oldScope claimedScope : Set Operation) : Prop :=
  q.reportedScope = claimedScope ∧
    ∃ certificate :
        TransportCert Operation Payload (Concept State Coordinate) Address
          ClaimVersion Error oldScope claimedScope,
      ValidTransportCert semantics certificate record q.concept
          (Version semantics q.concept) ∧
        (q.condition ↔
          GivenPremises certificate ∧ certificate.transportAssumption.Holds)

/-- Overreach is a strict scope expansion, correctly identifying the concept's
old scope and the report's claimed scope, without a license for that report. -/
def Overreach
    {Operation State Coordinate Payload Address ClaimVersion Error : Type*}
    (scope : Concept State Coordinate -> Set Operation)
    (semantics :
      ClaimSemantics Operation (Concept State Coordinate) Address ClaimVersion)
    (record : TruthRecord Operation Payload Address ClaimVersion Error)
    (q : TransportReport Operation State Coordinate)
    (oldScope claimedScope : Set Operation) : Prop :=
  oldScope ⊂ claimedScope ∧
    scope q.concept = oldScope ∧
    q.reportedScope = claimedScope ∧
    ¬LicensedReport semantics record q oldScope claimedScope

/- CAS tolerance gap: section 35 informally assumes that the record space
carries a distance, but it does not declare the comparison and supremum
operations on abstract `Delta`, or the laws for those operations, that Lean
needs for the later `≤` and above-threshold notation. No abstract tolerance
predicate or theorem is claimed here. The concrete Boolean false neighbor below
checks only the scope-expansion phenomenon. This comment and the matching Scribe
paragraph are human-readable only: they register neither digestion coverage nor
an unresolved subitem. Ingest currently has no path for a newly discovered
unresolved subitem; that machine-registration gap is tracked by issue #3066. -/

/-- Restricting the canonical escape residual to a concrete old and expanded
scope witnesses `Closed_J(S,T)` without `Closed_J'(S,T)`. -/
theorem domain_expansion_reopens_completion :
    ∃ oldScope claimedScope : Set Bool,
      oldScope ⊂ claimedScope ∧
        ∃ system target : Concept Bool Bool,
          defectRelation
              (fun operation : ↑oldScope => system operation)
              (fun operation : ↑oldScope => target operation) = ∅ ∧
            defectRelation
              (fun operation : ↑claimedScope => system operation)
              (fun operation : ↑claimedScope => target operation) ≠ ∅ := by
  refine ⟨{false}, Set.univ, Set.ssubset_iff_exists.mpr ?_,
    (fun _ => false), id, ?_, ?_⟩
  · exact ⟨Set.subset_univ _, true, Set.mem_univ true, by simp⟩
  · ext pair
    simp only [Set.mem_empty_iff_false, iff_false, defectRelation,
      Set.mem_setOf_eq]
    rintro ⟨_, targetDifferent⟩
    have leftFalse : (pair.1 : Bool) = false := by
      simpa only [Set.mem_singleton_iff] using pair.1.property
    have rightFalse : (pair.2 : Bool) = false := by
      simpa only [Set.mem_singleton_iff] using pair.2.property
    exact targetDifferent (leftFalse.trans rightFalse.symm)
  · rw [← Set.nonempty_iff_ne_empty]
    exact ⟨(⟨false, Set.mem_univ false⟩, ⟨true, Set.mem_univ true⟩),
      rfl, Bool.false_ne_true⟩

/-- The source-valid clauses in one public package: licensing,
unconditionalization, condition retention, overreach, reopening local
completion, and the licensed route to an unconditional report. The tolerance
clause is excluded because the source does not provide the operations and laws
needed to formalize its informal distance-based notation over abstract `Delta`. -/
theorem overreach_without_license
    {Operation State Coordinate Payload Address ClaimVersion Error : Type*}
    (scope : Concept State Coordinate -> Set Operation)
    (semantics :
      ClaimSemantics Operation (Concept State Coordinate) Address ClaimVersion)
    (record : TruthRecord Operation Payload Address ClaimVersion Error)
    (q : TransportReport Operation State Coordinate)
    (oldScope claimedScope : Set Operation) :
    (LicensedReport semantics record q oldScope claimedScope ↔
      q.reportedScope = claimedScope ∧
        ∃ certificate :
            TransportCert Operation Payload (Concept State Coordinate) Address
              ClaimVersion Error oldScope claimedScope,
          ValidTransportCert semantics certificate record q.concept
              (Version semantics q.concept) ∧
            (q.condition ↔ GivenPremises certificate ∧
              certificate.transportAssumption.Holds)) ∧
    (LicensedReport semantics record q oldScope claimedScope ->
      q.condition ->
      ∃ certificate :
          TransportCert Operation Payload (Concept State Coordinate) Address
            ClaimVersion Error oldScope claimedScope,
        ValidTransportCert semantics certificate record q.concept
            (Version semantics q.concept) ∧
          GivenPremises certificate ∧
          certificate.transportAssumption.Holds) ∧
    (LicensedReport semantics record q oldScope claimedScope ->
      ∃ certificate :
          TransportCert Operation Payload (Concept State Coordinate) Address
            ClaimVersion Error oldScope claimedScope,
        ValidTransportCert semantics certificate record q.concept
            (Version semantics q.concept) ∧
          (q.condition ↔ GivenPremises certificate ∧
            certificate.transportAssumption.Holds) ∧
          ((¬GivenPremises certificate ∨
            ¬certificate.transportAssumption.Holds) -> ¬q.condition)) ∧
    (Overreach scope semantics record q oldScope claimedScope ↔
      oldScope ⊂ claimedScope ∧
        scope q.concept = oldScope ∧
        q.reportedScope = claimedScope ∧
        ¬LicensedReport semantics record q oldScope claimedScope) ∧
    (∃ localScope expandedScope : Set Bool,
      localScope ⊂ expandedScope ∧
        ∃ system target : Concept Bool Bool,
          defectRelation
              (fun operation : ↑localScope => system operation)
              (fun operation : ↑localScope => target operation) = ∅ ∧
            defectRelation
              (fun operation : ↑expandedScope => system operation)
              (fun operation : ↑expandedScope => target operation) ≠ ∅) ∧
    (∀ certificate :
        TransportCert Operation Payload (Concept State Coordinate) Address
          ClaimVersion Error oldScope claimedScope,
      q.reportedScope = claimedScope ->
      ValidTransportCert semantics certificate record q.concept
        (Version semantics q.concept) ->
      GivenPremises certificate ->
      certificate.transportAssumption.Holds ->
      LicensedReport semantics record { q with condition := True }
        oldScope claimedScope) := by
  refine ⟨Iff.rfl, ?_, ?_, Iff.rfl, ?_, ?_⟩
  · rintro ⟨_, certificate, certificateValid, exactCondition⟩ conditionHolds
    exact ⟨certificate, certificateValid,
      (exactCondition.mp conditionHolds).1,
      (exactCondition.mp conditionHolds).2⟩
  · rintro ⟨_, certificate, certificateValid, exactCondition⟩
    refine ⟨certificate, certificateValid, exactCondition, ?_⟩
    rintro (premisesMissing | assumptionMissing) conditionHolds
    · exact premisesMissing (exactCondition.mp conditionHolds).1
    · exact assumptionMissing (exactCondition.mp conditionHolds).2
  · exact domain_expansion_reopens_completion
  · intro certificate reportedScopeMatches certificateValid
      premisesHold assumptionHolds
    refine ⟨reportedScopeMatches, certificate, certificateValid, ?_⟩
    simp [premisesHold, assumptionHolds]

/-- Downstream probe: the public package exposes both premise proofs from an
unconditional licensed report; they are not proof-local assumptions. -/
example
    {Operation State Coordinate Payload Address ClaimVersion Error : Type*}
    (scope : Concept State Coordinate -> Set Operation)
    (semantics :
      ClaimSemantics Operation (Concept State Coordinate) Address ClaimVersion)
    (record : TruthRecord Operation Payload Address ClaimVersion Error)
    (q : TransportReport Operation State Coordinate)
    (oldScope claimedScope : Set Operation)
    (licensed : LicensedReport semantics record q oldScope claimedScope)
    (unconditional : q.condition) :
    ∃ certificate :
        TransportCert Operation Payload (Concept State Coordinate) Address
          ClaimVersion Error oldScope claimedScope,
      ValidTransportCert semantics certificate record q.concept
          (Version semantics q.concept) ∧
        GivenPremises certificate ∧
        certificate.transportAssumption.Holds := by
  exact (overreach_without_license scope semantics record q
    oldScope claimedScope).2.1
      licensed unconditional

namespace FiniteLicensedWitness

def semantics : ClaimSemantics Bool (Concept Bool Bool) Nat Nat where
  claimAddress _claim := 11
  version _claim := 7
  claimOn _claim domain := domain = FiniteWitness.target

def prediction :
    FalsifiablePrediction Bool (Concept Bool Bool)
      FiniteWitness.source FiniteWitness.target where
  definedAt z := z = true
  failsAt z := z = true
  refutes z _claim := z = true
  nonemptyFailure := by
    exact ⟨true, FiniteWitness.true_mem_target_difference, rfl, rfl⟩

def certificate :
    TransportCert Bool Unit (Concept Bool Bool) Nat Nat Nat
      FiniteWitness.source FiniteWitness.target where
  receipt := FiniteWitness.receipt
  transportAssumption := FiniteWitness.assumption
  falsifiablePrediction := prediction

theorem valid_certificate_for_report :
    ValidTransportCert semantics certificate FiniteWitness.record id 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ReceiptMatches, ClaimAddress, semantics, certificate,
      FiniteWitness.receipt, FiniteWitness.record]
  · simp [GivenPremises, TransportAssumption.Holds, ClaimOn, semantics,
      certificate, FiniteWitness.assumption]
  · intro z hz
    change z ∈ Set.univ ∧ z ∉ ({false} : Set Bool) at hz
    cases z
    · exact (hz.2 (by rfl)).elim
    · rfl
  · exact ⟨true, FiniteWitness.true_mem_target_difference, rfl, rfl, rfl⟩

def impossibleSemantics : ClaimSemantics Bool (Concept Bool Bool) Nat Nat where
  claimAddress _claim := 11
  version _claim := 7
  claimOn _claim _domain := False

end FiniteLicensedWitness

/-- A concrete certificate satisfying every clause of the canonical validity
definition licenses an unconditional report, and that license blocks overreach. -/
example :
    let q : TransportReport Bool Bool Bool :=
      { concept := id, reportedScope := Set.univ, condition := True }
    LicensedReport FiniteLicensedWitness.semantics FiniteWitness.record
        q FiniteWitness.source FiniteWitness.target ∧
      ¬Overreach (fun _ => FiniteWitness.source)
        FiniteLicensedWitness.semantics FiniteWitness.record
        q FiniteWitness.source FiniteWitness.target := by
  dsimp
  have licensed :
      LicensedReport FiniteLicensedWitness.semantics FiniteWitness.record
        { concept := id, reportedScope := Set.univ, condition := True }
        FiniteWitness.source FiniteWitness.target := by
    refine ⟨rfl, FiniteLicensedWitness.certificate,
      FiniteLicensedWitness.valid_certificate_for_report, ?_⟩
    simp [GivenPremises, TransportAssumption.Holds,
      FiniteLicensedWitness.certificate, FiniteWitness.assumption]
  exact ⟨licensed, fun overreach => overreach.2.2.2 licensed⟩

/-- With the same finite scope expansion, semantics that make the transported
claim false cannot license an unconditional report, so the report overreaches. -/
example :
    let q : TransportReport Bool Bool Bool :=
      { concept := id, reportedScope := Set.univ, condition := True }
    Overreach (fun _ => FiniteWitness.source)
      FiniteLicensedWitness.impossibleSemantics FiniteWitness.record
      q FiniteWitness.source FiniteWitness.target := by
  dsimp
  refine ⟨Set.ssubset_iff_exists.mpr ?_, rfl, rfl, ?_⟩
  · exact ⟨Set.subset_univ _, true, Set.mem_univ true,
      by simp [FiniteWitness.source]⟩
  · rintro ⟨_, certificate, certificateValid, exactCondition⟩
    have claimOn := certificateValid.2.1 (exactCondition.mp True.intro)
    change False at claimOn
    exact claimOn

/-- On the finite operation and reading type `Bool`, the canonical closure is
empty on the old singleton and nonempty after expansion. -/
example :
    let oldScope : Set Bool := {false}
    let claimedScope : Set Bool := Set.univ
    let observed : Concept Bool Bool := fun _ => false
    let expected : Concept Bool Bool := id
    defectRelation
          (fun operation : ↑oldScope => observed operation)
          (fun operation : ↑oldScope => expected operation) = ∅ ∧
      defectRelation
          (fun operation : ↑claimedScope => observed operation)
          (fun operation : ↑claimedScope => expected operation) ≠ ∅ := by
  dsimp only
  constructor
  · ext pair
    simp only [Set.mem_empty_iff_false, iff_false, defectRelation,
      Set.mem_setOf_eq]
    rintro ⟨_, targetDifferent⟩
    have leftFalse : (pair.1 : Bool) = false := by
      simpa only [Set.mem_singleton_iff] using pair.1.property
    have rightFalse : (pair.2 : Bool) = false := by
      simpa only [Set.mem_singleton_iff] using pair.2.property
    exact targetDifferent (leftFalse.trans rightFalse.symm)
  · rw [← Set.nonempty_iff_ne_empty]
    exact ⟨(⟨false, Set.mem_univ false⟩, ⟨true, Set.mem_univ true⟩),
      rfl, Bool.false_ne_true⟩

/-- Positive control: an identity readout leaves no target escape residual on
either member of the same strict scope expansion. -/
example :
    let oldScope : Set Bool := {false}
    let claimedScope : Set Bool := Set.univ
    let system : Concept Bool Bool := id
    let target : Concept Bool Bool := id
    defectRelation
        (fun operation : ↑oldScope => system operation)
        (fun operation : ↑oldScope => target operation) = ∅ ∧
      defectRelation
        (fun operation : ↑claimedScope => system operation)
        (fun operation : ↑claimedScope => target operation) = ∅ := by
  dsimp only
  constructor <;> ext pair <;> simp [defectRelation]

namespace FalseNeighborWitness

/-- A valid certificate whose declared premise is false. Its conditional
transport clause is valid vacuously, but it cannot discharge an unconditional
report. -/
def conditionalAssumption : TransportAssumption where
  givenPremises := False
  preservedStructures := True
  usesSelectionMechanism := False
  selectionMechanismPreserved := False
  usesInterventionConsistency := False
  interventionConsistencyPreserved := False
  usesCovariateTransformation := False
  covariateTransformationPreserved := False
  usesLossStability := False
  lossStabilityPreserved := False

def conditionalCertificate :
    TransportCert Bool Unit (Concept Bool Bool) Nat Nat Nat
      FiniteWitness.source FiniteWitness.target where
  receipt := FiniteWitness.receipt
  transportAssumption := conditionalAssumption
  falsifiablePrediction := FiniteLicensedWitness.prediction

theorem valid_conditional_certificate :
    ValidTransportCert FiniteLicensedWitness.impossibleSemantics
      conditionalCertificate FiniteWitness.record id 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [ReceiptMatches, ClaimAddress,
      FiniteLicensedWitness.impossibleSemantics, conditionalCertificate,
      FiniteWitness.receipt, FiniteWitness.record]
  · simp [GivenPremises, TransportAssumption.Holds, ClaimOn,
      FiniteLicensedWitness.impossibleSemantics, conditionalCertificate,
      conditionalAssumption]
  · intro z hz
    change z ∈ Set.univ ∧ z ∉ ({false} : Set Bool) at hz
    cases z
    · exact (hz.2 (by rfl)).elim
    · rfl
  · exact ⟨true, FiniteWitness.true_mem_target_difference, rfl, rfl, rfl⟩

def wrongScopeReport : TransportReport Bool Bool Bool :=
  { concept := id, reportedScope := FiniteWitness.source, condition := True }

def conditionalReport : TransportReport Bool Bool Bool :=
  { concept := id, reportedScope := FiniteWitness.target, condition := False }

def unconditionalReport : TransportReport Bool Bool Bool :=
  { concept := id, reportedScope := FiniteWitness.target, condition := True }

theorem licensed_conditional_report :
    LicensedReport FiniteLicensedWitness.impossibleSemantics FiniteWitness.record
      conditionalReport FiniteWitness.source FiniteWitness.target := by
  refine ⟨rfl, conditionalCertificate, valid_conditional_certificate, ?_⟩
  simp [conditionalReport, GivenPremises, TransportAssumption.Holds,
    conditionalCertificate, conditionalAssumption]

theorem licensed_unconditional_report :
    LicensedReport FiniteLicensedWitness.semantics FiniteWitness.record
      unconditionalReport FiniteWitness.source FiniteWitness.target := by
  refine ⟨rfl, FiniteLicensedWitness.certificate,
    FiniteLicensedWitness.valid_certificate_for_report, ?_⟩
  simp [unconditionalReport, GivenPremises, TransportAssumption.Holds,
    FiniteLicensedWitness.certificate, FiniteWitness.assumption]

theorem unconditional_report_not_licensed_by_impossible_semantics :
    ¬LicensedReport FiniteLicensedWitness.impossibleSemantics FiniteWitness.record
      unconditionalReport FiniteWitness.source FiniteWitness.target := by
  rintro ⟨_, certificate, certificateValid, exactCondition⟩
  have claimOn := certificateValid.2.1 (exactCondition.mp True.intro)
  change False at claimOn
  exact claimOn

def booleanDeviation (readings : Bool × Bool) : Bool :=
  if readings.1 = readings.2 then false else true

def observed : Concept Bool Bool := fun _ => false

def expected : Concept Bool Bool := id

end FalseNeighborWitness

/-- False neighbor for clause 1: certificate data without the report-scope
equality does not license a report that stores the old scope. -/
theorem false_neighbor_license_without_reported_scope :
    ¬((∃ certificate :
          TransportCert Bool Unit (Concept Bool Bool) Nat Nat Nat
            FiniteWitness.source FiniteWitness.target,
        ValidTransportCert FiniteLicensedWitness.semantics certificate
            FiniteWitness.record FalseNeighborWitness.wrongScopeReport.concept 7 ∧
          (FalseNeighborWitness.wrongScopeReport.condition ↔
            GivenPremises certificate ∧ certificate.transportAssumption.Holds)) →
      LicensedReport FiniteLicensedWitness.semantics FiniteWitness.record
        FalseNeighborWitness.wrongScopeReport
        FiniteWitness.source FiniteWitness.target) := by
  intro weakLicense
  have certificateData :
      ∃ certificate :
          TransportCert Bool Unit (Concept Bool Bool) Nat Nat Nat
            FiniteWitness.source FiniteWitness.target,
        ValidTransportCert FiniteLicensedWitness.semantics certificate
            FiniteWitness.record FalseNeighborWitness.wrongScopeReport.concept 7 ∧
          (FalseNeighborWitness.wrongScopeReport.condition ↔
            GivenPremises certificate ∧ certificate.transportAssumption.Holds) := by
    refine ⟨FiniteLicensedWitness.certificate,
      FiniteLicensedWitness.valid_certificate_for_report, ?_⟩
    simp [FalseNeighborWitness.wrongScopeReport, GivenPremises,
      TransportAssumption.Holds, FiniteLicensedWitness.certificate,
      FiniteWitness.assumption]
  have scopeMatch := (weakLicense certificateData).1
  change FiniteWitness.source = FiniteWitness.target at scopeMatch
  have trueInSource : true ∈ FiniteWitness.source := by
    rw [scopeMatch]
    exact Set.mem_univ true
  exact FiniteWitness.true_mem_target_difference.2 trueInSource

/-- False neighbor for clause 2: licensing alone does not discharge the
retained report condition and therefore cannot expose all premise proofs. -/
theorem false_neighbor_license_elimination_without_condition :
    ¬(LicensedReport FiniteLicensedWitness.impossibleSemantics
          FiniteWitness.record FalseNeighborWitness.conditionalReport
          FiniteWitness.source FiniteWitness.target →
      ∃ certificate :
          TransportCert Bool Unit (Concept Bool Bool) Nat Nat Nat
            FiniteWitness.source FiniteWitness.target,
        ValidTransportCert FiniteLicensedWitness.impossibleSemantics certificate
            FiniteWitness.record FalseNeighborWitness.conditionalReport.concept 7 ∧
          GivenPremises certificate ∧ certificate.transportAssumption.Holds) := by
  intro weakElimination
  rcases weakElimination FalseNeighborWitness.licensed_conditional_report with
    ⟨certificate, certificateValid, premisesHold, assumptionHolds⟩
  have claimOn := certificateValid.2.1 ⟨premisesHold, assumptionHolds⟩
  change False at claimOn
  exact claimOn

/-- False neighbor for clause 3: replacing exact condition retention by the
one-way implication from obligations to the report condition admits an
unconditional report with an undischarged premise. -/
theorem false_neighbor_one_way_condition_retention :
    ¬((FalseNeighborWitness.unconditionalReport.reportedScope =
          FiniteWitness.target ∧
        ∃ certificate :
            TransportCert Bool Unit (Concept Bool Bool) Nat Nat Nat
              FiniteWitness.source FiniteWitness.target,
          ValidTransportCert FiniteLicensedWitness.impossibleSemantics certificate
              FiniteWitness.record
              FalseNeighborWitness.unconditionalReport.concept 7 ∧
            ((GivenPremises certificate ∧ certificate.transportAssumption.Holds) →
              FalseNeighborWitness.unconditionalReport.condition)) →
      LicensedReport FiniteLicensedWitness.impossibleSemantics FiniteWitness.record
        FalseNeighborWitness.unconditionalReport
        FiniteWitness.source FiniteWitness.target) := by
  intro weakRetention
  apply FalseNeighborWitness.unconditional_report_not_licensed_by_impossible_semantics
  apply weakRetention
  refine ⟨rfl, FalseNeighborWitness.conditionalCertificate,
    FalseNeighborWitness.valid_conditional_certificate, ?_⟩
  intro _
  trivial

/-- False neighbor for clause 4: strict expansion and the two scope equations
do not imply overreach when the report is licensed. -/
theorem false_neighbor_scope_expansion_is_always_overreach :
    ¬((FiniteWitness.source ⊂ FiniteWitness.target ∧
          (fun _ : Concept Bool Bool => FiniteWitness.source)
              FalseNeighborWitness.unconditionalReport.concept =
            FiniteWitness.source ∧
          FalseNeighborWitness.unconditionalReport.reportedScope =
            FiniteWitness.target) →
      Overreach (fun _ : Concept Bool Bool => FiniteWitness.source)
        FiniteLicensedWitness.semantics FiniteWitness.record
        FalseNeighborWitness.unconditionalReport
        FiniteWitness.source FiniteWitness.target) := by
  intro weakOverreach
  have strictExpansion : FiniteWitness.source ⊂ FiniteWitness.target := by
    refine Set.ssubset_iff_exists.mpr ?_
    exact ⟨Set.subset_univ _, true, Set.mem_univ true,
      by simp [FiniteWitness.source]⟩
  have overreach := weakOverreach ⟨strictExpansion, rfl, rfl⟩
  exact overreach.2.2.2 FalseNeighborWitness.licensed_unconditional_report

/-- False neighbor for the unresolved tolerance clause. With the concrete
Boolean convention that deviation `false` is within tolerance, old-scope
tolerance need not survive strict expansion. This does not supply the abstract
comparison or supremum operations and laws missing from the formal interface. -/
theorem false_neighbor_tolerance_survives_scope_expansion :
    ¬((∀ operation ∈ FiniteWitness.source,
          FalseNeighborWitness.booleanDeviation
              (FalseNeighborWitness.observed operation,
                FalseNeighborWitness.expected operation) = false) →
      ∀ operation ∈ FiniteWitness.target,
        FalseNeighborWitness.booleanDeviation
            (FalseNeighborWitness.observed operation,
              FalseNeighborWitness.expected operation) = false) := by
  intro weakTolerance
  have oldTolerance :
      ∀ operation ∈ FiniteWitness.source,
        FalseNeighborWitness.booleanDeviation
            (FalseNeighborWitness.observed operation,
              FalseNeighborWitness.expected operation) = false := by
    intro operation operationInOld
    have operationFalse : operation = false := by
      simpa [FiniteWitness.source] using operationInOld
    subst operation
    simp [FalseNeighborWitness.booleanDeviation, FalseNeighborWitness.observed,
      FalseNeighborWitness.expected]
  have expandedTolerance := weakTolerance oldTolerance
  have atTrue := expandedTolerance true (by simp [FiniteWitness.target])
  change true = false at atTrue
  cases atTrue

/-- False neighbor for clause 6: emptiness of the canonical defect relation on
the old scope does not imply emptiness on the expanded scope. -/
theorem false_neighbor_closure_survives_scope_expansion :
    ¬(defectRelation
          (fun operation : ↑FiniteWitness.source =>
            FalseNeighborWitness.observed operation)
          (fun operation : ↑FiniteWitness.source =>
            FalseNeighborWitness.expected operation) = ∅ →
      defectRelation
          (fun operation : ↑FiniteWitness.target =>
            FalseNeighborWitness.observed operation)
          (fun operation : ↑FiniteWitness.target =>
            FalseNeighborWitness.expected operation) = ∅) := by
  intro weakClosure
  have oldClosed :
      defectRelation
          (fun operation : ↑FiniteWitness.source =>
            FalseNeighborWitness.observed operation)
          (fun operation : ↑FiniteWitness.source =>
            FalseNeighborWitness.expected operation) = ∅ := by
    ext pair
    simp only [Set.mem_empty_iff_false, iff_false, defectRelation,
      Set.mem_setOf_eq]
    rintro ⟨_, targetDifferent⟩
    have leftFalse : (pair.1 : Bool) = false := by
      simpa only [FiniteWitness.source, Set.mem_singleton_iff] using
        pair.1.property
    have rightFalse : (pair.2 : Bool) = false := by
      simpa only [FiniteWitness.source, Set.mem_singleton_iff] using
        pair.2.property
    exact targetDifferent (leftFalse.trans rightFalse.symm)
  have expandedClosed := weakClosure oldClosed
  have reopened :
      (⟨false, Set.mem_univ false⟩, ⟨true, Set.mem_univ true⟩) ∈
        defectRelation
          (fun operation : ↑FiniteWitness.target =>
            FalseNeighborWitness.observed operation)
          (fun operation : ↑FiniteWitness.target =>
            FalseNeighborWitness.expected operation) := by
    exact ⟨rfl, Bool.false_ne_true⟩
  rw [expandedClosed] at reopened
  exact reopened

/-- False neighbor for clause 7: validity alone does not license an
unconditional report; the premises and preservation obligations are required. -/
theorem false_neighbor_validity_alone_deconditions_report :
    ¬(ValidTransportCert FiniteLicensedWitness.impossibleSemantics
          FalseNeighborWitness.conditionalCertificate FiniteWitness.record id 7 →
      LicensedReport FiniteLicensedWitness.impossibleSemantics FiniteWitness.record
        FalseNeighborWitness.unconditionalReport
        FiniteWitness.source FiniteWitness.target) := by
  intro weakDeconditioning
  exact FalseNeighborWitness.unconditional_report_not_licensed_by_impossible_semantics
    (weakDeconditioning FalseNeighborWitness.valid_conditional_certificate)

#print axioms overreach_without_license

end D5.S3.ConceptDynamics.Transport.OverreachWithoutLicense
