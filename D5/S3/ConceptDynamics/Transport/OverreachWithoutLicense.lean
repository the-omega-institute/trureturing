/- GID: D5/S3/ConceptDynamics/Transport/OverreachWithoutLicense
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/OverreachWithoutLicense
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Licensed reports retain transport conditions and expansion reopens completion. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-08-24):
   * Type-shape search
     `rg -n --glob '*.lean' '^(structure|def) .*Report|TransportReport|
     LicensedReport|ValidTransportCert|TransportCert' D5/S3/ConceptDynamics`
     found `ProvenanceReport` and `ReportProfile`; they carry provenance checks
     or state-indexed messages, not a concept, claimed scope, and retained
     transport condition. No transport-license carrier or predicate was found.
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
     found no license or overreach definition. Exact hit `Concept` is reused.
     Exact hit `defectRelation` remains the sole target-confusion relation; no
     residual, escape, or pair-relation definition is introduced here.
   * Pinned-Mathlib shape search
     `rg -n 'def EqOn|theorem ssubset_iff_exists|ssubset_iff_exists'
     .lake/packages/mathlib/Mathlib/Data/Set .lake/packages/mathlib/Mathlib`
     found `Set.EqOn` and `Set.ssubset_iff_exists`; both are used directly for
     local agreement and for selecting an operation in the expanded domain. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transport.OverreachWithoutLicense

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- A transport report contains the transported concept, the scope it claims,
and the condition retained in the report. -/
structure TransportReport (Operation State Coordinate : Type*) where
  concept : Concept State Coordinate
  reportedScope : Set Operation
  condition : Prop

/-- An abstract certificate-validity predicate is nontrivial when it rejects at
least one input. A licensed report supplies an accepted input separately, so
the two obligations together rule out both constant interpretations. -/
def NontrivialTransportCert
    {Operation State Coordinate Certificate Version : Type*}
    (validTransportCert : Certificate -> Concept State Coordinate ->
      Set Operation -> Set Operation -> Version -> Prop) : Prop :=
  ∃ certificate concept oldScope claimedScope certificateVersion,
    ¬validTransportCert certificate concept oldScope claimedScope
      certificateVersion

/-- A report is licensed exactly when certificate validity is nontrivial and a
valid transport certificate retains its full premises and transport assumption
as the report condition. The separate certificate-validity module owns the
abstract predicate and can later supply the stronger concrete interpretation. -/
def LicensedReport
    {Operation State Coordinate Certificate Version : Type*}
    (validTransportCert : Certificate -> Concept State Coordinate ->
      Set Operation -> Set Operation -> Version -> Prop)
    (version : Concept State Coordinate -> Version)
    (givenPremises transportAssumption : Certificate -> Prop)
    (q : TransportReport Operation State Coordinate)
    (oldScope claimedScope : Set Operation) : Prop :=
  NontrivialTransportCert validTransportCert ∧
    q.reportedScope = claimedScope ∧
      ∃ certificate,
        validTransportCert certificate q.concept oldScope claimedScope
            (version q.concept) ∧
          (q.condition ↔
            givenPremises certificate ∧ transportAssumption certificate)

/-- Overreach is a strict scope expansion, correctly identifying the concept's
old scope and the report's claimed scope, without a license for that report. -/
def Overreach
    {Operation State Coordinate Certificate Version : Type*}
    (scope : Concept State Coordinate -> Set Operation)
    (validTransportCert : Certificate -> Concept State Coordinate ->
      Set Operation -> Set Operation -> Version -> Prop)
    (version : Concept State Coordinate -> Version)
    (givenPremises transportAssumption : Certificate -> Prop)
    (q : TransportReport Operation State Coordinate)
    (oldScope claimedScope : Set Operation) : Prop :=
  oldScope ⊂ claimedScope ∧
    scope q.concept = oldScope ∧
    q.reportedScope = claimedScope ∧
    ¬LicensedReport validTransportCert version givenPremises
      transportAssumption q oldScope claimedScope

/-- Two records agree within a supplied deviation threshold on every operation
in a given scope. -/
def WithinTolerance
    {Operation Reading : Type*}
    (deviation : Reading -> Reading -> Nat) (epsilon : Nat)
    (operationScope : Set Operation)
    (observed expected : Concept Operation Reading) : Prop :=
  ∀ operation ∈ operationScope,
    deviation (observed operation) (expected operation) ≤ epsilon

/-- Local completion is pointwise agreement on the operations in scope. This
uses Mathlib's canonical restricted-equality predicate. -/
def LocallyClosed
    {Operation Reading : Type*} (operationScope : Set Operation)
    (system target : Concept Operation Reading) : Prop :=
  Set.EqOn system target operationScope

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

/-- A strict scope expansion with two distinguishable readings admits a local
completion on the old scope that is not complete on the claimed scope. -/
theorem domain_expansion_reopens_local_completion
    {Operation Reading : Type*} {oldScope claimedScope : Set Operation}
    (strictExpansion : oldScope ⊂ claimedScope)
    (distinctReadings : ∃ ordinary exceptional : Reading,
      ordinary ≠ exceptional) :
    ∃ system target : Concept Operation Reading,
      LocallyClosed oldScope system target ∧
        ¬LocallyClosed claimedScope system target := by
  classical
  rcases Set.ssubset_iff_exists.mp strictExpansion with
    ⟨_, operation, operationInClaimed, operationNotInOld⟩
  rcases distinctReadings with ⟨ordinary, exceptional, different⟩
  let system : Concept Operation Reading := fun _ => ordinary
  let target : Concept Operation Reading := fun current =>
    if current = operation then exceptional else ordinary
  refine ⟨system, target, ?_, ?_⟩
  · intro current currentInOld
    have currentNeOperation : current ≠ operation := by
      intro same
      subst current
      exact operationNotInOld currentInOld
    simp [system, target, currentNeOperation]
  · intro closedOnClaimed
    have equalAtNew := closedOnClaimed operationInClaimed
    simp only [system, target, if_pos] at equalAtNew
    exact different equalAtNew

/-- The source clauses in one public package: licensing, unconditionalization,
condition retention, overreach, the expansion counterexample, reopening local
completion, and the licensed route to an unconditional report. -/
theorem overreach_without_license
    {Operation State Coordinate Certificate Version : Type*}
    (scope : Concept State Coordinate -> Set Operation)
    (validTransportCert : Certificate -> Concept State Coordinate ->
      Set Operation -> Set Operation -> Version -> Prop)
    (version : Concept State Coordinate -> Version)
    (givenPremises transportAssumption : Certificate -> Prop)
    (q : TransportReport Operation State Coordinate)
    (oldScope claimedScope : Set Operation) :
    (LicensedReport validTransportCert version givenPremises
        transportAssumption q oldScope claimedScope ↔
      NontrivialTransportCert validTransportCert ∧
        q.reportedScope = claimedScope ∧
          ∃ certificate,
            validTransportCert certificate q.concept oldScope claimedScope
                (version q.concept) ∧
              (q.condition ↔ givenPremises certificate ∧
                transportAssumption certificate)) ∧
    (LicensedReport validTransportCert version givenPremises
        transportAssumption q oldScope claimedScope ->
      q.condition ->
      ∃ certificate,
        validTransportCert certificate q.concept oldScope claimedScope
            (version q.concept) ∧
          givenPremises certificate ∧ transportAssumption certificate) ∧
    (LicensedReport validTransportCert version givenPremises
        transportAssumption q oldScope claimedScope ->
      ∃ certificate,
        validTransportCert certificate q.concept oldScope claimedScope
            (version q.concept) ∧
          (q.condition ↔ givenPremises certificate ∧
            transportAssumption certificate) ∧
          ((¬givenPremises certificate ∨
            ¬transportAssumption certificate) -> ¬q.condition)) ∧
    (Overreach scope validTransportCert version givenPremises
        transportAssumption q oldScope claimedScope ↔
      oldScope ⊂ claimedScope ∧
        scope q.concept = oldScope ∧
        q.reportedScope = claimedScope ∧
        ¬LicensedReport validTransportCert version givenPremises
          transportAssumption q oldScope claimedScope) ∧
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
    (∀ {localScope expandedScope : Set Operation},
      localScope ⊂ expandedScope ->
      (∃ ordinary exceptional : Coordinate, ordinary ≠ exceptional) ->
      ∃ system target : Concept Operation Coordinate,
        LocallyClosed localScope system target ∧
          ¬LocallyClosed expandedScope system target) ∧
    (∀ certificate,
      NontrivialTransportCert validTransportCert ->
      q.reportedScope = claimedScope ->
      validTransportCert certificate q.concept oldScope claimedScope
        (version q.concept) ->
      givenPremises certificate ->
      transportAssumption certificate ->
      LicensedReport validTransportCert version givenPremises
        transportAssumption { q with condition := True }
        oldScope claimedScope) := by
  refine ⟨Iff.rfl, ?_, ?_, Iff.rfl, ?_, ?_, ?_⟩
  · rintro ⟨_, _, certificate, certificateValid, exactCondition⟩ conditionHolds
    exact ⟨certificate, certificateValid,
      (exactCondition.mp conditionHolds).1,
      (exactCondition.mp conditionHolds).2⟩
  · rintro ⟨_, _, certificate, certificateValid, exactCondition⟩
    refine ⟨certificate, certificateValid, exactCondition, ?_⟩
    rintro (premisesMissing | assumptionMissing) conditionHolds
    · exact premisesMissing (exactCondition.mp conditionHolds).1
    · exact assumptionMissing (exactCondition.mp conditionHolds).2
  · intro deviation epsilon localScope expandedScope strictExpansion
      unchangedWithin largeDeviation
    exact domain_expansion_breaks_tolerance deviation epsilon strictExpansion
      unchangedWithin largeDeviation
  · intro localScope expandedScope strictExpansion distinctReadings
    exact domain_expansion_reopens_local_completion strictExpansion distinctReadings
  · intro certificate nontrivial reportedScopeMatches certificateValid
      premisesHold assumptionHolds
    refine ⟨nontrivial, reportedScopeMatches, certificate, certificateValid, ?_⟩
    simp [premisesHold, assumptionHolds]

/-- Downstream probe: the public package exposes both premise proofs from an
unconditional licensed report; they are not proof-local assumptions. -/
example
    {Operation State Coordinate Certificate Version : Type*}
    (scope : Concept State Coordinate -> Set Operation)
    (validTransportCert : Certificate -> Concept State Coordinate ->
      Set Operation -> Set Operation -> Version -> Prop)
    (version : Concept State Coordinate -> Version)
    (givenPremises transportAssumption : Certificate -> Prop)
    (q : TransportReport Operation State Coordinate)
    (oldScope claimedScope : Set Operation)
    (licensed : LicensedReport validTransportCert version givenPremises
      transportAssumption q oldScope claimedScope)
    (unconditional : q.condition) :
    ∃ certificate,
      validTransportCert certificate q.concept oldScope claimedScope
          (version q.concept) ∧
        givenPremises certificate ∧ transportAssumption certificate := by
  exact (overreach_without_license scope validTransportCert version
    givenPremises transportAssumption q oldScope claimedScope).2.1
      licensed unconditional

/-- A constantly true certificate predicate cannot license any report. -/
example :
    let validTransportCert :
        Unit -> Concept Bool Bool -> Set Bool -> Set Bool -> Unit -> Prop :=
      fun _ _ _ _ _ => True
    let q : TransportReport Bool Bool Bool :=
      { concept := id, reportedScope := Set.univ, condition := True }
    ¬LicensedReport validTransportCert (fun _ => ()) (fun _ => True)
      (fun _ => True) q {false} Set.univ := by
  simp [LicensedReport, NontrivialTransportCert]

/-- A concrete finite interpretation accepts one certificate and rejects
another. Its unconditional report is licensed, and that license blocks
overreach. -/
example :
    let validTransportCert :
        Bool -> Concept Bool Bool -> Set Bool -> Set Bool -> Unit -> Prop :=
      fun certificate _ _ _ _ => certificate = true
    let q : TransportReport Bool Bool Bool :=
      { concept := id, reportedScope := Set.univ, condition := True }
    LicensedReport validTransportCert (fun _ => ()) (fun _ => True)
        (fun _ => True) q {false} Set.univ ∧
      ¬Overreach (fun _ => {false}) validTransportCert (fun _ => ())
        (fun _ => True) (fun _ => True) q {false} Set.univ := by
  dsimp
  have nontrivial :
      NontrivialTransportCert
        (fun (certificate : Bool) (_ : Concept Bool Bool) (_ _ : Set Bool)
          (_ : Unit) => certificate = true) := by
    exact ⟨false, id, ∅, ∅, (), by simp⟩
  have licensed :
      LicensedReport
        (fun (certificate : Bool) (_ : Concept Bool Bool) (_ _ : Set Bool)
          (_ : Unit) => certificate = true)
        (fun _ => ()) (fun _ => True) (fun _ => True)
        { concept := id, reportedScope := Set.univ, condition := True }
        {false} Set.univ := by
    exact ⟨nontrivial, rfl, true, rfl, by simp⟩
  exact ⟨licensed, fun overreach => overreach.2.2.2 licensed⟩

/-- With the same finite scope expansion but no valid certificate, the report
is genuinely overreaching; the predicates are therefore not constant. -/
example :
    let validTransportCert :
        Unit -> Concept Bool Bool -> Set Bool -> Set Bool -> Unit -> Prop :=
      fun _ _ _ _ _ => False
    let q : TransportReport Bool Bool Bool :=
      { concept := id, reportedScope := Set.univ, condition := True }
    Overreach (fun _ => {false}) validTransportCert (fun _ => ())
      (fun _ => True) (fun _ => True) q {false} Set.univ := by
  dsimp
  refine ⟨Set.ssubset_iff_exists.mpr ?_, rfl, rfl, ?_⟩
  · exact ⟨Set.subset_univ _, true, Set.mem_univ true, by simp⟩
  · simp [LicensedReport, NontrivialTransportCert]

/-- On the finite operation and reading type `Bool`, the records agree on the
old singleton but both tolerance and local completion fail after expansion. -/
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
      LocallyClosed oldScope observed expected ∧
      ¬LocallyClosed claimedScope observed expected := by
  dsimp [WithinTolerance, LocallyClosed, Set.EqOn]
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
  · intro operation operationInOld
    simp only [Set.mem_singleton_iff] at operationInOld
    subst operation
    rfl
  · intro closedOnClaimed
    have atTrue := closedOnClaimed (Set.mem_univ true)
    exact Bool.false_ne_true atTrue

#print axioms overreach_without_license

end D5.S3.ConceptDynamics.Transport.OverreachWithoutLicense
