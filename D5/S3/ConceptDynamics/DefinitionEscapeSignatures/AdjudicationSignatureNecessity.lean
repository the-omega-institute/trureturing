/- GID: D5/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeSignatures/AdjudicationSignatureNecessity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every sufficient signature coordinate has a finite deletion witness. -/

import D5.S3.ConceptDynamics.DefinitionEscapeSignatures.AdjudicationSignatureSufficiency

/-!
# Coordinate necessity for the adjudication signature

OP1 proves signature sufficiency for `NonAnticipating`, `AdmissibleJudge`, and
`ScientificGain`, but refutes it for target laundering.  Thus the surviving
OP2 obligation has four coordinate directions, not a four-by-four matrix of
coordinates and consumers.  The witnesses below use `NonAnticipating` for the
freeze-visibility, decision-visibility, and direct-contamination directions,
and `AdmissibleJudge` for the role-projection direction.

The target-laundering branch needs restatement rather than a necessity witness:
its OP1 antecedent is false because the signature omits whole-commitment report
identity and `frozenAt`.  The imported
`target_laundering_signature_counterexample` is the frozen decision of that
branch; it is not reproved here.

Statement echo for OP2:

* The finite record set `Z` and selected evidence are `records` and `true` in
  all four directions.
* `SameOut` is `SameOutNA records true` in the first three directions and
  `SameOutAJ records true` in the role direction.
* Each direction proposition states equality of the three unablated fields of
  `AdjudicationSignature`, inequality of the selected field, and equivalence of
  the positive consumer with the negation of the negative consumer.
* The source permits a different already-sufficient consumer in each direction;
  no target-laundering consumer is selected, so the old/new extra clause is not
  triggered.  There are exactly four direction propositions.

Library-search audit trail (2026-08-30):

* Exact-name and body-shape searches for adjudication-signature coordinate
  necessity, deletion witnesses, and the four signature field names found no
  existing declaration in `D5` or pinned Mathlib.
* The only repository dependency is the schema-v5 frozen OP1 owner
  `AdjudicationSignatureSufficiency`; all carriers, consumers, and signature
  fields below are reused from it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.DefinitionEscapeSignatures.AdjudicationSignatureNecessity

open D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.ScientificGainGeneralizationReversal
open D5.S3.ConceptDynamics.Governance.TargetLaunderingCriterion
open D5.S3.ConceptDynamics.DefinitionEscapeSignatures.AdjudicationSignatureSufficiency

namespace FiniteWitness

abbrev Snapshot := AdjudicationSnapshot Bool Bool Unit Bool Bool ()
abbrev Ledger := VersionedRoleLedger Bool Bool Unit Bool Unit Bool

/-- The common nonempty finite record set. -/
def records : Finset Bool := {true}

/-- Evidence is unseen at freeze and visible at decision. -/
def stagedFiltration : EvidenceFiltration Bool Bool where
  seen event := if event then Set.univ else ∅
  monotone := by
    intro i j hij
    cases i <;> cases j
    · exact Set.Subset.rfl
    · exact Set.empty_subset _
    · exact False.elim ((by decide : ¬(true ≤ false)) hij)
    · exact Set.Subset.rfl

/-- Evidence is invisible at both distinguished events. -/
def invisibleFiltration : EvidenceFiltration Bool Bool where
  seen _ := ∅
  monotone := by
    intro _ _ _
    exact Set.Subset.rfl

/-- Evidence is visible at both distinguished events. -/
def visibleFiltration : EvidenceFiltration Bool Bool where
  seen _ := Set.univ
  monotone := by
    intro _ _ _
    exact Set.Subset.rfl

/-- A finite snapshot with fixed event and time boundaries. -/
def snapshot (filtration : EvidenceFiltration Bool Bool)
    (dependencies : Set Bool) : Snapshot where
  freezeEvent := false
  decisionEvent := true
  frozenAt := false
  decidedAt := true
  freezeBeforeDecision := by decide
  timeBeforeDecision := by decide
  filtration := filtration
  dependencyClosure := ∅
  evidenceDependencies := dependencies

def clean : Snapshot := snapshot stagedFiltration ∅
def freezeExposed : Snapshot := snapshot visibleFiltration ∅
def decisionHidden : Snapshot := snapshot invisibleFiltration ∅
def contaminated : Snapshot := snapshot stagedFiltration {true}

/-- The common empty ledger for the first three coordinate directions. -/
def emptyLedger : Ledger where
  events := []
  uniqueEventIds := by simp
  strictEventOrder := by simp
  indexRespectsRound := by simp
  indexRespectsTime := by simp

theorem empty_valid (history : Snapshot) : ValidTrace emptyLedger history := by
  simp [ValidTrace, emptyLedger]

theorem empty_role_projection (history : Snapshot)
    (valid : ValidTrace emptyLedger history) :
    roleExistenceProjection records emptyLedger history valid = ∅ := by
  ext atom
  simp [roleExistenceProjection, InAdjudicationPrefix, emptyLedger]

/-- One in-prefix adjudication event for the role-projection direction. -/
def judgeEvent : RoleUseEvent Bool Bool Unit Bool Unit Bool where
  eventId := true
  evidence := true
  round := ()
  role := .adjudicate
  dependencies := ∅
  protocol := ()
  usedAt := true

def judgeLedger : Ledger where
  events := [judgeEvent]
  uniqueEventIds := by simp [judgeEvent]
  strictEventOrder := by simp
  indexRespectsRound := by
    intro event later eventMem laterMem _
    simp only [List.mem_singleton] at eventMem laterMem
    subst event
    subst later
    exact le_rfl
  indexRespectsTime := by
    intro event later eventMem laterMem _
    simp only [List.mem_singleton] at eventMem laterMem
    subst event
    subst later
    exact le_rfl

theorem judge_valid : ValidTrace judgeLedger clean := by
  intro event eventMem
  simp only [judgeLedger, List.mem_singleton] at eventMem
  subst event
  simp [judgeEvent, clean, snapshot, stagedFiltration]

end FiniteWitness

open FiniteWitness

/-- Deleting freeze visibility loses non-anticipation while all three other
signature fields and SameOut remain fixed. -/
def FreezeVisibilityDirection : Prop :=
  let positive := adjudicationSignature records emptyLedger clean (empty_valid clean)
  let negative := adjudicationSignature records emptyLedger freezeExposed
    (empty_valid freezeExposed)
  SameOutNA records true ∧
    positive.decisionVisible = negative.decisionVisible ∧
    positive.directlyContaminated = negative.directlyContaminated ∧
    positive.roleProjection = negative.roleProjection ∧
    positive.freezeVisible ≠ negative.freezeVisible ∧
    (NonAnticipating clean true ↔ ¬NonAnticipating freezeExposed true)

/-- Deleting decision visibility loses non-anticipation while all three other
signature fields and SameOut remain fixed. -/
def DecisionVisibilityDirection : Prop :=
  let positive := adjudicationSignature records emptyLedger clean (empty_valid clean)
  let negative := adjudicationSignature records emptyLedger decisionHidden
    (empty_valid decisionHidden)
  SameOutNA records true ∧
    positive.freezeVisible = negative.freezeVisible ∧
    positive.directlyContaminated = negative.directlyContaminated ∧
    positive.roleProjection = negative.roleProjection ∧
    positive.decisionVisible ≠ negative.decisionVisible ∧
    (NonAnticipating clean true ↔ ¬NonAnticipating decisionHidden true)

/-- Deleting direct contamination loses non-anticipation while all three other
signature fields and SameOut remain fixed. -/
def DirectContaminationDirection : Prop :=
  let positive := adjudicationSignature records emptyLedger clean (empty_valid clean)
  let negative := adjudicationSignature records emptyLedger contaminated
    (empty_valid contaminated)
  SameOutNA records true ∧
    positive.freezeVisible = negative.freezeVisible ∧
    positive.decisionVisible = negative.decisionVisible ∧
    positive.roleProjection = negative.roleProjection ∧
    positive.directlyContaminated ≠ negative.directlyContaminated ∧
    (NonAnticipating clean true ↔ ¬NonAnticipating contaminated true)

/-- Deleting the role projection loses admissible judging while all three
visibility/contamination fields and SameOut remain fixed. -/
def RoleProjectionDirection : Prop :=
  let positive := adjudicationSignature records judgeLedger clean judge_valid
  let negative := adjudicationSignature records emptyLedger clean (empty_valid clean)
  SameOutAJ records true ∧
    positive.freezeVisible = negative.freezeVisible ∧
    positive.decisionVisible = negative.decisionVisible ∧
    positive.directlyContaminated = negative.directlyContaminated ∧
    positive.roleProjection ≠ negative.roleProjection ∧
    (AdmissibleJudge judgeLedger clean judge_valid true ↔
      ¬AdmissibleJudge emptyLedger clean (empty_valid clean) true)

theorem freeze_visibility_direction : FreezeVisibilityDirection := by
  dsimp only [FreezeVisibilityDirection]
  refine ⟨⟨by simp [records]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact (empty_role_projection clean (empty_valid clean)).trans
      (empty_role_projection freezeExposed (empty_valid freezeExposed)).symm
  · simp [records, adjudicationSignature, clean, freezeExposed, snapshot,
      stagedFiltration, visibleFiltration]
  · simp [clean, freezeExposed, snapshot, stagedFiltration,
      visibleFiltration, NonAnticipating]

theorem decision_visibility_direction : DecisionVisibilityDirection := by
  dsimp only [DecisionVisibilityDirection]
  refine ⟨⟨by simp [records]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact (empty_role_projection clean (empty_valid clean)).trans
      (empty_role_projection decisionHidden (empty_valid decisionHidden)).symm
  · simp [records, adjudicationSignature, clean, decisionHidden, snapshot,
      stagedFiltration, invisibleFiltration]
  · simp [clean, decisionHidden, snapshot, stagedFiltration,
      invisibleFiltration, NonAnticipating]

theorem direct_contamination_direction : DirectContaminationDirection := by
  dsimp only [DirectContaminationDirection]
  refine ⟨⟨by simp [records]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · exact (empty_role_projection clean (empty_valid clean)).trans
      (empty_role_projection contaminated (empty_valid contaminated)).symm
  · simp [records, adjudicationSignature, clean, contaminated, snapshot]
  · simp [clean, contaminated, snapshot, stagedFiltration, NonAnticipating]

theorem role_projection_direction : RoleProjectionDirection := by
  dsimp only [RoleProjectionDirection]
  refine ⟨⟨by simp [records]⟩, ?_⟩
  simp [records, adjudicationSignature, roleExistenceProjection, judgeLedger,
    judgeEvent, emptyLedger, clean, snapshot, stagedFiltration,
    AdmissibleJudge, RolesAt, InAdjudicationPrefix, AdaptiveUseInClosure,
    closureTouchBit, RelevantSignatureRole]

/-- OP2 for the post-OP1 surviving branches: the four directions each have a
finite witness with SameOut, equality off the selected coordinate, inequality
at that coordinate, and opposite consumer truth values. -/
theorem adjudication_signature_coordinate_necessity :
    FreezeVisibilityDirection ∧
      DecisionVisibilityDirection ∧
      DirectContaminationDirection ∧
      RoleProjectionDirection := by
  exact ⟨freeze_visibility_direction,
    decision_visibility_direction,
    direct_contamination_direction,
    role_projection_direction⟩

#print axioms freeze_visibility_direction
#print axioms decision_visibility_direction
#print axioms direct_contamination_direction
#print axioms role_projection_direction
#print axioms adjudication_signature_coordinate_necessity

end D5.S3.ConceptDynamics.DefinitionEscapeSignatures.AdjudicationSignatureNecessity
