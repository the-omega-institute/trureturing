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
     `rg -n 'def EqOn|theorem ssubset_iff_exists|ssubset_iff_exists'
     .lake/packages/mathlib/Mathlib/Data/Set .lake/packages/mathlib/Mathlib`
     found `Set.EqOn` and `Set.ssubset_iff_exists`; they are used directly for
     tolerance agreement and for selecting an operation in the expanded domain. -/

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

/-- Two records agree within a supplied deviation threshold on every operation
in a given scope. -/
def WithinTolerance
    {Operation Reading : Type*}
    (deviation : Reading -> Reading -> Nat) (epsilon : Nat)
    (operationScope : Set Operation)
    (observed expected : Concept Operation Reading) : Prop :=
  ∀ operation ∈ operationScope,
    deviation (observed operation) (expected operation) ≤ epsilon

/-- A new operation and an available above-threshold deviation give records
that remain unchanged and within tolerance on the old scope but fail on the
expanded scope. -/
theorem domain_expansion_breaks_tolerance
    {Operation Reading : Type*}
    (deviation : Reading -> Reading -> Nat) (epsilon : Nat)
    {oldScope claimedScope : Set Operation}
    (strictExpansion : oldScope ⊂ claimedScope)
    (unchangedWithin : ∀ reading, deviation reading reading ≤ epsilon)
    (largeDeviation : ∃ ordinary exceptional : Reading,
      epsilon < deviation ordinary exceptional) :
    ∃ observed expected : Concept Operation Reading,
      Set.EqOn observed expected oldScope ∧
        WithinTolerance deviation epsilon oldScope observed expected ∧
        ¬WithinTolerance deviation epsilon claimedScope observed expected := by
  classical
  rcases Set.ssubset_iff_exists.mp strictExpansion with
    ⟨_, operation, operationInClaimed, operationNotInOld⟩
  rcases largeDeviation with ⟨ordinary, exceptional, aboveThreshold⟩
  let observed : Concept Operation Reading := fun _ => ordinary
  let expected : Concept Operation Reading := fun current =>
    if current = operation then exceptional else ordinary
  refine ⟨observed, expected, ?_, ?_, ?_⟩
  · intro current currentInOld
    have currentNeOperation : current ≠ operation := by
      intro same
      subst current
      exact operationNotInOld currentInOld
    simp [observed, expected, currentNeOperation]
  · intro current currentInOld
    have currentNeOperation : current ≠ operation := by
      intro same
      subst current
      exact operationNotInOld currentInOld
    simpa [observed, expected, currentNeOperation] using unchangedWithin ordinary
  · intro withinClaimed
    have atNewOperation := withinClaimed operation operationInClaimed
    simp only [observed, expected, if_pos] at atNewOperation
    exact (not_le_of_gt aboveThreshold) atNewOperation

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

/-- The source clauses in one public package: licensing, unconditionalization,
condition retention, overreach, the expansion counterexample, reopening local
completion, and the licensed route to an unconditional report. -/
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
    (∀ (deviation : Coordinate -> Coordinate -> Nat) (epsilon : Nat)
        {localScope expandedScope : Set Operation},
      localScope ⊂ expandedScope ->
      (∀ reading, deviation reading reading ≤ epsilon) ->
      (∃ ordinary exceptional : Coordinate,
        epsilon < deviation ordinary exceptional) ->
      ∃ observed expected : Concept Operation Coordinate,
        Set.EqOn observed expected localScope ∧
          WithinTolerance deviation epsilon localScope observed expected ∧
          ¬WithinTolerance deviation epsilon expandedScope observed expected) ∧
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
  refine ⟨Iff.rfl, ?_, ?_, Iff.rfl, ?_, ?_, ?_⟩
  · rintro ⟨_, certificate, certificateValid, exactCondition⟩ conditionHolds
    exact ⟨certificate, certificateValid,
      (exactCondition.mp conditionHolds).1,
      (exactCondition.mp conditionHolds).2⟩
  · rintro ⟨_, certificate, certificateValid, exactCondition⟩
    refine ⟨certificate, certificateValid, exactCondition, ?_⟩
    rintro (premisesMissing | assumptionMissing) conditionHolds
    · exact premisesMissing (exactCondition.mp conditionHolds).1
    · exact assumptionMissing (exactCondition.mp conditionHolds).2
  · intro deviation epsilon localScope expandedScope strictExpansion
      unchangedWithin largeDeviation
    exact domain_expansion_breaks_tolerance deviation epsilon strictExpansion
      unchangedWithin largeDeviation
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

/-- On the finite operation and reading type `Bool`, the records agree on the
old singleton but both tolerance and canonical closure fail after expansion. -/
example :
    let deviation : Bool -> Bool -> Nat := fun left right =>
      if left = right then 0 else 1
    let oldScope : Set Bool := {false}
    let claimedScope : Set Bool := Set.univ
    let observed : Concept Bool Bool := fun _ => false
    let expected : Concept Bool Bool := id
    Set.EqOn observed expected oldScope ∧
      WithinTolerance deviation 0 oldScope observed expected ∧
      ¬WithinTolerance deviation 0 claimedScope observed expected ∧
      defectRelation
          (fun operation : ↑oldScope => observed operation)
          (fun operation : ↑oldScope => expected operation) = ∅ ∧
      defectRelation
          (fun operation : ↑claimedScope => observed operation)
          (fun operation : ↑claimedScope => expected operation) ≠ ∅ := by
  dsimp only [WithinTolerance, Set.EqOn]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro operation operationInOld
    simp only [Set.mem_singleton_iff] at operationInOld
    subst operation
    rfl
  · intro operation operationInOld
    simp only [Set.mem_singleton_iff] at operationInOld
    subst operation
    simp
  · intro withinClaimed
    have atTrue := withinClaimed true (Set.mem_univ true)
    simp at atTrue
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

#print axioms overreach_without_license

end D5.S3.ConceptDynamics.Transport.OverreachWithoutLicense
