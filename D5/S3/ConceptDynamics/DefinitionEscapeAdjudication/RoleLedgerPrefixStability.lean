/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RoleLedgerPrefixStability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/RoleLedgerPrefixStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Valid role traces reject unseen events; late appends preserve the frozen prefix. -/

import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-26):
   * `rg -n -i 'append.only.*prefix|prefix.*append.only|adjudication.*prefix|
     RolePrefixAtEvent|RolePrefixAtRound|RolePrefixAtTime|InAdjudicationPrefix|
     ValidTrace|event.*round.*time|tail.*decision' D5 --glob '*.lean'` found no
     event/round/time prefix-stability theorem.  `CancellationLedger` only
     proves a free-monoid left-factor statement and preservation of one event.
   * `rg -n -i 'append.*prefix|prefix.*append|filter.*append|mem.*append|
     take.*append|drop.*append' .lake/packages/mathlib/Mathlib --glob '*.lean'`
     found generic list and language lemmas, but no adjudication-ledger result.
   * Pinned Mathlib supplies `List.mem_append`; the proof below also uses the
     strict-after-decision premise to exclude every event in the appended tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/-- The five roles of one evidence-use event.  The prefix distinguishes this
full ledger record from the reduced role type in the frozen closure module. -/
inductive LedgerEvidenceRole
  | generate
  | tune
  | select
  | adjudicate
  | replicate
  deriving DecidableEq

/-- One role-ledger event with its unique index, epistemic role, dependencies,
protocol, round, and physical time. -/
structure RoleUseEvent
    (EventId Evidence Round Artifact Protocol Time : Type u) where
  eventId : EventId
  evidence : Evidence
  round : Round
  role : LedgerEvidenceRole
  dependencies : Set Artifact
  protocol : Protocol
  usedAt : Time

/-- Evidence visible at each event index, monotonically increasing with that
index. -/
structure VersionedEvidenceFiltration
    (EventId Evidence : Type u) [Preorder EventId] where
  seen : EventId -> Set Evidence
  monotone : forall {i j}, i <= j -> seen i ⊆ seen j

/-- A finite role log whose event identifiers are strictly ordered and whose
round and time coordinates do not decrease along the identifier order. -/
structure VersionedRoleLedger
    (EventId Evidence Round Artifact Protocol Time : Type u)
    [LinearOrder EventId] [Preorder Round] [Preorder Time] where
  events : List (RoleUseEvent EventId Evidence Round Artifact Protocol Time)
  uniqueEventIds : (events.map fun event => event.eventId).Nodup
  strictEventOrder :
    events.Pairwise (fun event later => event.eventId < later.eventId)
  indexRespectsRound : forall {event later},
    event ∈ events -> later ∈ events ->
      event.eventId <= later.eventId -> event.round <= later.round
  indexRespectsTime : forall {event later},
    event ∈ events -> later ∈ events ->
      event.eventId <= later.eventId -> event.usedAt <= later.usedAt

/-- Every recorded role event must use evidence visible at that event's own
index.  A consumer receives the whole proof rather than silently filtering bad
events. -/
def ValidRoleTrace
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (filtration : VersionedEvidenceFiltration EventId Evidence) : Prop :=
  forall event, event ∈ ledger.events ->
    event.evidence ∈ filtration.seen event.eventId

/-- One recorded event that is unseen at its own index invalidates the entire
role trace. -/
theorem invalid_trace_of_unseen_recorded_event
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (filtration : VersionedEvidenceFiltration EventId Evidence)
    (event : RoleUseEvent EventId Evidence Round Artifact Protocol Time)
    (recorded : event ∈ ledger.events)
    (unseen : event.evidence ∉ filtration.seen event.eventId) :
    Not (ValidRoleTrace ledger filtration) := by
  intro valid
  exact unseen (valid event recorded)

/-- The frozen adjudication prefix is the simultaneous event-index, round, and
time prefix of the role log. -/
def AdjudicationRolePrefix
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (decisionEvent : EventId) (decisionRound : Round) (decidedAt : Time) :
    Set (RoleUseEvent EventId Evidence Round Artifact Protocol Time) :=
  {event | event ∈ ledger.events ∧ event.eventId <= decisionEvent ∧
    event.round <= decisionRound ∧ event.usedAt <= decidedAt}

/-- The roles a record occupies in the frozen adjudication prefix.  Repeated
uses remain separate events and are collected relationally rather than stored
as a permanent property of the evidence record. -/
def RolesAtInPrefix
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (ledger : VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (decisionEvent : EventId) (decisionRound : Round) (decidedAt : Time)
    (record : Evidence) : Set LedgerEvidenceRole :=
  {role | exists event,
    event ∈ AdjudicationRolePrefix ledger decisionEvent decisionRound decidedAt ∧
      event.evidence = record ∧ event.round = decisionRound ∧ event.role = role}

/-- A later ledger is obtained by appending events whose identifiers are all
strictly beyond the frozen decision event. -/
def AppendOnlyRoleExtension
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (oldLedger newLedger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (decisionEvent : EventId) : Prop :=
  exists tail, newLedger.events = oldLedger.events ++ tail ∧
    forall event, event ∈ tail -> decisionEvent < event.eventId

/-- Appending only events strictly after the frozen decision index leaves the
entire old event/round/time adjudication prefix unchanged.  The two trace
hypotheses make the source's reject-the-whole-ledger precondition explicit. -/
theorem append_only_adjudication_role_prefix_unchanged
    {EventId Evidence Round Artifact Protocol Time : Type u}
    [LinearOrder EventId] [Preorder Round] [Preorder Time]
    (filtration : VersionedEvidenceFiltration EventId Evidence)
    (oldLedger newLedger :
      VersionedRoleLedger EventId Evidence Round Artifact Protocol Time)
    (decisionEvent : EventId) (decisionRound : Round) (decidedAt : Time)
    (_oldValid : ValidRoleTrace oldLedger filtration)
    (_newValid : ValidRoleTrace newLedger filtration)
    (appendOnly : AppendOnlyRoleExtension oldLedger newLedger decisionEvent) :
    AdjudicationRolePrefix newLedger decisionEvent decisionRound decidedAt =
      AdjudicationRolePrefix oldLedger decisionEvent decisionRound decidedAt := by
  rcases appendOnly with ⟨tail, events_eq, tail_after_decision⟩
  apply Set.ext
  intro event
  simp only [AdjudicationRolePrefix, Set.mem_setOf_eq]
  constructor
  · rintro ⟨inNew, beforeDecision, beforeRound, beforeTime⟩
    rw [events_eq] at inNew
    rcases List.mem_append.mp inNew with inOld | inTail
    · exact ⟨inOld, beforeDecision, beforeRound, beforeTime⟩
    · exact False.elim
        ((not_lt_of_ge beforeDecision) (tail_after_decision event inTail))
  · rintro ⟨inOld, beforeDecision, beforeRound, beforeTime⟩
    refine ⟨?_, beforeDecision, beforeRound, beforeTime⟩
    rw [events_eq]
    exact List.mem_append_left tail inOld

/-- The hypotheses are jointly inhabited by a valid empty frozen log and a
valid one-event extension whose sole event occurs strictly after the decision. -/
example :
    exists filtration : VersionedEvidenceFiltration Nat Bool,
      exists oldLedger newLedger :
        VersionedRoleLedger Nat Bool Nat Bool Unit Nat,
        ValidRoleTrace oldLedger filtration ∧
          ValidRoleTrace newLedger filtration ∧
          AppendOnlyRoleExtension oldLedger newLedger 0 ∧
          newLedger.events ≠ [] ∧
          AdjudicationRolePrefix newLedger 0 0 0 =
            AdjudicationRolePrefix oldLedger 0 0 0 := by
  let lateEvent : RoleUseEvent Nat Bool Nat Bool Unit Nat :=
    { eventId := 1
      evidence := true
      round := 1
      role := .tune
      dependencies := {true}
      protocol := ()
      usedAt := 1 }
  let filtration : VersionedEvidenceFiltration Nat Bool :=
    { seen := fun _ => Set.univ
      monotone := by
        intro _ _ _
        exact Set.Subset.rfl }
  let oldLedger : VersionedRoleLedger Nat Bool Nat Bool Unit Nat :=
    { events := []
      uniqueEventIds := by simp
      strictEventOrder := by simp
      indexRespectsRound := by simp
      indexRespectsTime := by simp }
  let newLedger : VersionedRoleLedger Nat Bool Nat Bool Unit Nat :=
    { events := [lateEvent]
      uniqueEventIds := by simp
      strictEventOrder := by simp
      indexRespectsRound := by
        intro event later inEvent inLater _
        simp only [List.mem_singleton] at inEvent inLater
        subst event
        subst later
        exact le_rfl
      indexRespectsTime := by
        intro event later inEvent inLater _
        simp only [List.mem_singleton] at inEvent inLater
        subst event
        subst later
        exact le_rfl }
  have oldValid : ValidRoleTrace oldLedger filtration := by
    simp [ValidRoleTrace, oldLedger]
  have newValid : ValidRoleTrace newLedger filtration := by
    simp [ValidRoleTrace, newLedger, filtration]
  have appended : AppendOnlyRoleExtension oldLedger newLedger 0 := by
    refine ⟨[lateEvent], ?_, ?_⟩
    · simp [oldLedger, newLedger]
    · intro event inTail
      simp only [List.mem_singleton] at inTail
      subst event
      simp [lateEvent]
  refine ⟨filtration, oldLedger, newLedger, oldValid, newValid, appended, ?_, ?_⟩
  · simp [newLedger]
  · exact append_only_adjudication_role_prefix_unchanged
      filtration oldLedger newLedger 0 0 0 oldValid newValid appended

#print axioms invalid_trace_of_unseen_recorded_event
#print axioms append_only_adjudication_role_prefix_unchanged

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
