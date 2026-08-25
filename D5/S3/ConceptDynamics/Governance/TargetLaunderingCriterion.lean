/- GID: D5/S3/ConceptDynamics/Governance/TargetLaunderingCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Governance/TargetLaunderingCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Target laundering requires coordinate change, regrading, and original attribution. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic

/- Library-search audit trail (2026-08-25):
   * Exact searches
     `rg -n -i 'target.*launder|launder.*target|TargetLaundering' D5 Blueprint`
     and searches for `PostArrivalProtectedChange`, `RegradeReport`, and
     `ProtectedCoordinates` returned no Lean declaration. The same names occur
     only in the DECT reference source's proposed formal interface.
   * Type-shape searches for `structure .*Commitment`, `structure .*Report`,
     `targetChain`, `weightSpec`, `regradedVerdict`, and `attributedTo` found no
     commitment/report structure with this field family. `TransportReport` and
     `TransportCert` concern scope transport, not post-arrival re-evaluation.
   * Synonym searches covered commitment/pledge/seal (承诺/冻结/封存),
     protected/guarded/coordinate (保护/受护/坐标),
     arrival/first-seen/filtration (到达/首次可达/滤过),
     regrade/reassess/evaluate/verdict (重评/复评/评价/裁决), and
     laundering/bleaching/whitewashing/tamper/retroactive
     (漂白/洗白/回写/篡改/追溯). Hits in ConceptDynamics concern target
     factorization, transport, or causal attribution and do not combine a
     protected-coordinate change with an actual revised evaluation.
   * `git grep -n -E '^(def|theorem|structure|inductive|abbrev) ' --
     D5/S3/ConceptDynamics/Governance D5/S3/ConceptDynamics/Attribution
     D5/S3/ConceptDynamics/Provenance D5/S3/ConceptDynamics/Transport`
     found no exact criterion. `TransportCertificateValidity` seals source
     coordinates for domain transport; `OverreachWithoutLicense` rejects
     unlicensed scope expansion. Neither records regrading or attribution.
     The brief-named `RoleAdmissionContaminationClosure` is absent from both
     this checkout and remote dev commit 48385266dc86.
   * Source closure: DECT lines 3625-3631 define arrival as first reachability
     in the access filtration, including infinity for evidence never seen; lines
     3755-3772 define the commitment and scope; lines 4872-4932 give proposed
     protected-coordinate and actual regrade-report interfaces. The draft at
     line 4927 retains only membership at the freeze event, whereas the atom at
     line 3994 requires strict arrival-before-time. The strict source formula is
     retained here without Nat, measurability, finiteness, or decidable equality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion

/-- The access-ledger filtration used to interpret arrival before a commitment event. -/
structure EvidenceFiltration (EventId Evidence : Type*) where
  precedes : EventId -> EventId -> Prop
  precedesRefl : forall event, precedes event event
  precedesTrans : forall {i j k}, precedes i j -> precedes j k -> precedes i k
  seen : EventId -> Set Evidence
  monotone : forall {i j}, precedes i j -> seen i <= seen j
  firstSeen : Evidence -> Option EventId
  seen_iff : forall {e k}, e ∈ seen k ↔
    ∃ arrival, firstSeen e = some arrival ∧ precedes arrival k

/-- Strict access-ledger order derived from the filtration's general preorder. -/
def StrictlyPrecedes {EventId Evidence : Type*}
    (filtration : EvidenceFiltration EventId Evidence)
    (first second : EventId) : Prop :=
  filtration.precedes first second ∧ ¬filtration.precedes second first

/-- A prospective commitment retains its event address, full scope, evaluation
coordinates, test plan, and finite typed artifact bundle. -/
structure ProspectiveCommitment
    (EventId TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec Artifact : Type*) where
  freezeEvent : EventId
  targetChain : TargetChain
  domain : Domain
  epsilon : Epsilon
  conditions : Condition
  comparator : Comparator
  testPlan : TestPlan
  baseline : Baseline
  weightSpec : WeightSpec
  committedArtifacts : Finset Artifact

/-- Exactly the seven coordinates protected by the source definition. -/
structure ProtectedCoordinates
    (TargetChain Domain Epsilon Condition Comparator Baseline WeightSpec : Type*) where
  targetChain : TargetChain
  domain : Domain
  epsilon : Epsilon
  conditions : Condition
  comparator : Comparator
  baseline : Baseline
  weightSpec : WeightSpec

/-- Direct projection of every protected coordinate from a commitment. -/
def protectedCoordinates
    {EventId TargetChain Domain Epsilon Condition Comparator TestPlan Baseline
      WeightSpec Artifact : Type*}
    (commitment : ProspectiveCommitment EventId TargetChain Domain Epsilon Condition
      Comparator TestPlan Baseline WeightSpec Artifact) :
    ProtectedCoordinates TargetChain Domain Epsilon Condition Comparator Baseline
      WeightSpec :=
  { targetChain := commitment.targetChain
    domain := commitment.domain
    epsilon := commitment.epsilon
    conditions := commitment.conditions
    comparator := commitment.comparator
    baseline := commitment.baseline
    weightSpec := commitment.weightSpec }

/-- A protected-coordinate change is post-arrival precisely when the ledger's
actual first-seen event strictly precedes the revised freeze event. -/
def PostArrivalProtectedChange
    {EventId Evidence TargetChain Domain Epsilon Condition Comparator TestPlan
      Baseline WeightSpec Artifact : Type*}
    (filtration : EvidenceFiltration EventId Evidence)
    (original revised : ProspectiveCommitment EventId TargetChain Domain Epsilon
      Condition Comparator TestPlan Baseline WeightSpec Artifact)
    (evidence : Evidence) : Prop :=
  ∃ arrival,
    filtration.firstSeen evidence = some arrival ∧
      StrictlyPrecedes filtration arrival revised.freezeEvent ∧
      protectedCoordinates revised ≠ protectedCoordinates original

/-- A regrade report cannot choose an arbitrary truth label: its verdict field
is accompanied by an equality to the actual evaluation of its revised commitment. -/
structure RegradeReport
    (Commitment Evidence Verdict EventId : Type*)
    (evaluate : Commitment -> Evidence -> Verdict) where
  original : Commitment
  revised : Commitment
  evidence : Evidence
  regradedVerdict : Verdict
  regradesOldRound : regradedVerdict = evaluate revised evidence
  attributedTo : Commitment
  occurredAt : EventId

/-- Reporting a concrete verdict as success for a commitment is a pair of
record equalities, not a caller-supplied proposition. -/
def ReportedAsSuccess
    {Commitment Evidence Verdict EventId : Type*}
    {evaluate : Commitment -> Evidence -> Verdict}
    (report : RegradeReport Commitment Evidence Verdict EventId evaluate)
    (verdict : Verdict) (commitment : Commitment) : Prop :=
  report.regradedVerdict = verdict ∧ report.attributedTo = commitment

/-- The report regrades the original round with the revised coordinates and the
old evidence, at the revised commitment event, using the actual evaluation. -/
def RegradesOldRound
    {Commitment Evidence Verdict EventId : Type*}
    {evaluate : Commitment -> Evidence -> Verdict}
    (original revised : Commitment) (evidence : Evidence) (revisedAt : EventId)
    (report : RegradeReport Commitment Evidence Verdict EventId evaluate) : Prop :=
  report.original = original ∧
    report.revised = revised ∧
    report.evidence = evidence ∧
    report.regradedVerdict = evaluate revised evidence ∧
    report.occurredAt = revisedAt

/-- Attribution to the original commitment consumes the actual revised
evaluation selected by `evaluate`; it has no free propositional certificate. -/
def AttributesToOriginalCommitment
    {Commitment Evidence Verdict EventId : Type*}
    (evaluate : Commitment -> Evidence -> Verdict)
    (original revised : Commitment) (evidence : Evidence)
    (report : RegradeReport Commitment Evidence Verdict EventId evaluate) : Prop :=
  ReportedAsSuccess report (evaluate revised evidence) original

/-- Target laundering is the conjunction of post-arrival protected change,
actual regrading of the old round, and attribution to the original commitment. -/
def TargetLaundering
    {EventId Evidence TargetChain Domain Epsilon Condition Comparator TestPlan
      Baseline WeightSpec Artifact Verdict : Type*}
    (evaluate :
      ProspectiveCommitment EventId TargetChain Domain Epsilon Condition Comparator
        TestPlan Baseline WeightSpec Artifact -> Evidence -> Verdict)
    (filtration : EvidenceFiltration EventId Evidence)
    (original revised : ProspectiveCommitment EventId TargetChain Domain Epsilon
      Condition Comparator TestPlan Baseline WeightSpec Artifact)
    (evidence : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId TargetChain Domain Epsilon Condition Comparator
        TestPlan Baseline WeightSpec Artifact)
      Evidence Verdict EventId evaluate) : Prop :=
  PostArrivalProtectedChange filtration original revised evidence ∧
    RegradesOldRound original revised evidence revised.freezeEvent report ∧
    AttributesToOriginalCommitment evaluate original revised evidence report

/-- The source criterion, with all three clauses and the report's actual
evaluation witness retained. -/
theorem target_laundering_criterion
    {EventId Evidence TargetChain Domain Epsilon Condition Comparator TestPlan
      Baseline WeightSpec Artifact Verdict : Type*}
    (evaluate :
      ProspectiveCommitment EventId TargetChain Domain Epsilon Condition Comparator
        TestPlan Baseline WeightSpec Artifact -> Evidence -> Verdict)
    (filtration : EvidenceFiltration EventId Evidence)
    (original revised : ProspectiveCommitment EventId TargetChain Domain Epsilon
      Condition Comparator TestPlan Baseline WeightSpec Artifact)
    (evidence : Evidence)
    (report : RegradeReport
      (ProspectiveCommitment EventId TargetChain Domain Epsilon Condition Comparator
        TestPlan Baseline WeightSpec Artifact)
      Evidence Verdict EventId evaluate) :
    TargetLaundering evaluate filtration original revised evidence report ↔
      PostArrivalProtectedChange filtration original revised evidence ∧
        RegradesOldRound original revised evidence revised.freezeEvent report ∧
        AttributesToOriginalCommitment evaluate original revised evidence report :=
  Iff.rfl

namespace FiniteWitness

abbrev EventId := Fin 3

abbrev Commitment :=
  ProspectiveCommitment EventId Unit Unit Unit Bool Unit Unit Unit Unit (Fin 1)

def filtration : EvidenceFiltration EventId Bool where
  precedes := fun i j => i.val <= j.val
  precedesRefl := fun event => Nat.le_refl event.val
  precedesTrans := fun first second => Nat.le_trans first second
  seen := fun _ => Set.univ
  monotone := by
    intro i j hij evidence evidenceSeen
    exact evidenceSeen
  firstSeen := fun _ => some 0
  seen_iff := by
    intro evidence event
    simp

def emptyFiltration : EvidenceFiltration EventId Bool where
  precedes := fun i j => i.val <= j.val
  precedesRefl := fun event => Nat.le_refl event.val
  precedesTrans := fun first second => Nat.le_trans first second
  seen := fun _ => ∅
  monotone := by
    intro i j hij evidence evidenceSeen
    exact evidenceSeen
  firstSeen := fun _ => none
  seen_iff := by simp

def original : Commitment where
  freezeEvent := 1
  targetChain := ()
  domain := ()
  epsilon := ()
  conditions := false
  comparator := ()
  testPlan := ()
  baseline := ()
  weightSpec := ()
  committedArtifacts := ∅

def revised : Commitment where
  freezeEvent := 2
  targetChain := ()
  domain := ()
  epsilon := ()
  conditions := true
  comparator := ()
  testPlan := ()
  baseline := ()
  weightSpec := ()
  committedArtifacts := ∅

def evaluate : Commitment -> Bool -> Bool := fun _ _ => false

def validReport : RegradeReport Commitment Bool Bool EventId evaluate where
  original := original
  revised := revised
  evidence := true
  regradedVerdict := false
  regradesOldRound := rfl
  attributedTo := original
  occurredAt := revised.freezeEvent

def wrongRoundReport : RegradeReport Commitment Bool Bool EventId evaluate where
  original := revised
  revised := revised
  evidence := true
  regradedVerdict := false
  regradesOldRound := rfl
  attributedTo := original
  occurredAt := revised.freezeEvent

def wrongAttributionReport : RegradeReport Commitment Bool Bool EventId evaluate where
  original := original
  revised := revised
  evidence := true
  regradedVerdict := false
  regradesOldRound := rfl
  attributedTo := revised
  occurredAt := revised.freezeEvent

theorem original_ne_revised : original ≠ revised := by
  intro commitmentsEqual
  have conditionsEqual := congrArg (fun commitment : Commitment => commitment.conditions)
    commitmentsEqual
  simp [original, revised] at conditionsEqual

theorem protected_coordinates_changed :
    protectedCoordinates revised ≠ protectedCoordinates original := by
  intro coordinatesEqual
  have conditionsEqual := congrArg
    (fun coordinates : ProtectedCoordinates Unit Unit Unit Bool Unit Unit Unit =>
      coordinates.conditions)
    coordinatesEqual
  simp [protectedCoordinates, original, revised] at conditionsEqual

end FiniteWitness

/-- Positive control: the protected condition changes after arrival, the report
carries the actual revised evaluation, attribution targets the original
commitment, and both old and revised evaluations nevertheless have one value. -/
theorem same_verdict_target_laundering :
    TargetLaundering FiniteWitness.evaluate FiniteWitness.filtration
        FiniteWitness.original FiniteWitness.revised true FiniteWitness.validReport ∧
      FiniteWitness.evaluate FiniteWitness.original true =
        FiniteWitness.evaluate FiniteWitness.revised true := by
  constructor
  · simp only [TargetLaundering]
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨0, rfl, ?_, FiniteWitness.protected_coordinates_changed⟩
      simp [StrictlyPrecedes, FiniteWitness.filtration, FiniteWitness.revised]
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  · rfl

/-- False-side control for clause one: with an empty access filtration, the
same actual report still regrades and attributes correctly, but is not post-arrival. -/
theorem false_neighbor_no_post_arrival_change :
    ¬PostArrivalProtectedChange FiniteWitness.emptyFiltration
        FiniteWitness.original FiniteWitness.revised true ∧
      RegradesOldRound FiniteWitness.original FiniteWitness.revised true
        FiniteWitness.revised.freezeEvent FiniteWitness.validReport ∧
      AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.original
        FiniteWitness.revised true FiniteWitness.validReport := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  rintro ⟨arrival, firstSeen, _arrivalBefore, _coordinatesChanged⟩
  simp [FiniteWitness.emptyFiltration] at firstSeen

/-- False-side control for clause two: the report contains a genuine revised
evaluation and correct attribution, but names the revised commitment as original. -/
theorem false_neighbor_no_old_round_regrade :
    PostArrivalProtectedChange FiniteWitness.filtration
        FiniteWitness.original FiniteWitness.revised true ∧
      ¬RegradesOldRound FiniteWitness.original FiniteWitness.revised true
        FiniteWitness.revised.freezeEvent FiniteWitness.wrongRoundReport ∧
      AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.original
        FiniteWitness.revised true FiniteWitness.wrongRoundReport := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨0, rfl, ?_, FiniteWitness.protected_coordinates_changed⟩
    simp [StrictlyPrecedes, FiniteWitness.filtration, FiniteWitness.revised]
  · intro regrades
    exact FiniteWitness.original_ne_revised regrades.1.symm
  · exact ⟨rfl, rfl⟩

/-- False-side control for clause three: the report contains the actual
re-evaluation and correct round identities, but attributes it to the revision. -/
theorem false_neighbor_no_original_attribution :
    PostArrivalProtectedChange FiniteWitness.filtration
        FiniteWitness.original FiniteWitness.revised true ∧
      RegradesOldRound FiniteWitness.original FiniteWitness.revised true
        FiniteWitness.revised.freezeEvent FiniteWitness.wrongAttributionReport ∧
      ¬AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.original
        FiniteWitness.revised true FiniteWitness.wrongAttributionReport := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨0, rfl, ?_, FiniteWitness.protected_coordinates_changed⟩
    simp [StrictlyPrecedes, FiniteWitness.filtration, FiniteWitness.revised]
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro attributes
    exact FiniteWitness.original_ne_revised attributes.2.symm

/-- Fail-closed consumer for every named positive and false-side witness. -/
theorem target_laundering_nondegeneracy :
    (TargetLaundering FiniteWitness.evaluate FiniteWitness.filtration
        FiniteWitness.original FiniteWitness.revised true FiniteWitness.validReport ∧
      FiniteWitness.evaluate FiniteWitness.original true =
        FiniteWitness.evaluate FiniteWitness.revised true) ∧
    (¬PostArrivalProtectedChange FiniteWitness.emptyFiltration
        FiniteWitness.original FiniteWitness.revised true ∧
      RegradesOldRound FiniteWitness.original FiniteWitness.revised true
        FiniteWitness.revised.freezeEvent FiniteWitness.validReport ∧
      AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.original
        FiniteWitness.revised true FiniteWitness.validReport) ∧
    (PostArrivalProtectedChange FiniteWitness.filtration
        FiniteWitness.original FiniteWitness.revised true ∧
      ¬RegradesOldRound FiniteWitness.original FiniteWitness.revised true
        FiniteWitness.revised.freezeEvent FiniteWitness.wrongRoundReport ∧
      AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.original
        FiniteWitness.revised true FiniteWitness.wrongRoundReport) ∧
    (PostArrivalProtectedChange FiniteWitness.filtration
        FiniteWitness.original FiniteWitness.revised true ∧
      RegradesOldRound FiniteWitness.original FiniteWitness.revised true
        FiniteWitness.revised.freezeEvent FiniteWitness.wrongAttributionReport ∧
      ¬AttributesToOriginalCommitment FiniteWitness.evaluate FiniteWitness.original
        FiniteWitness.revised true FiniteWitness.wrongAttributionReport) := by
  exact ⟨same_verdict_target_laundering,
    false_neighbor_no_post_arrival_change,
    false_neighbor_no_old_round_regrade,
    false_neighbor_no_original_attribution⟩

#print axioms target_laundering_criterion
#print axioms target_laundering_nondegeneracy

end D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion
