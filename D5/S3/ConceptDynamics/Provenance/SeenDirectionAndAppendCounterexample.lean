/- GID: D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Concrete early-append witness for the strict post-decision boundary. -/

import D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure

/- Library-search audit trail (2026-08-25):
   * `rg -n 'AppendOnlyExtension|admissible_judge_append_invariant|'\
       'early append|post-decision' D5/S3/ConceptDynamics \
       docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md`
     found the reusable invariant in the imported role module and the source's
     strict post-decision condition; no existing concrete early-append witness.
   * `git grep -n -E \
       '^def |^  def |^structure |^inductive |^abbrev |^theorem ' -- \
       D5/S3/ConceptDynamics/Provenance | head -60`
     found the role module's existing append-invariance theorem and no semantic
     early-append counterexample. This file adds only its concrete neighbor.
   * `grep -rl \
       'RoleAdmissionContaminationClosure\|SeenDirectionAndAppendCounterexample' \
       Golden/Frozen/accepted/*.json`
     returned no paths, so neither module is frozen.
   * `nl -ba docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md | \
       sed -n '3680,3730p'`
     confirmed at line 3721 that only tail events strictly after the decision
     event preserve old-round admission. The witness below violates exactly
     that premise while keeping the source ledger and snapshot types.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.SeenDirectionAndAppendCounterexample

open D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure

private def semanticFiltration : EvidenceFiltration Nat Bool :=
  { seen := fun cutoff =>
      {evidence | (evidence = true /\ 1 <= cutoff) \/
        (evidence = false /\ 3 <= cutoff)}
    monotone := by
      intro i j hij evidence seen
      rcases seen with seen | seen
      · exact Or.inl ⟨seen.1, seen.2.trans hij⟩
      · exact Or.inr ⟨seen.1, seen.2.trans hij⟩ }

private def semanticSnapshot : AdjudicationSnapshot Nat Bool Nat Bool Nat 7 :=
  { freezeEvent := 1
    decisionEvent := 4
    frozenAt := 1
    decidedAt := 3
    freezeBeforeDecision := by decide
    timeBeforeDecision := by decide
    filtration := semanticFiltration
    artifactDependsOn := fun source target => source = target
    commitmentRoots := {true}
    evidenceDependsOn := fun source target => source = target
    evidenceDependencies := {true} }

private def semanticAdjudicateEvent : UseEvent Nat Bool Nat Bool Unit Nat :=
  { eventId := 3
    evidence := false
    round := 7
    role := .adjudicate
    dependencies := ∅
    protocol := ()
    usedAt := 2 }

private def semanticAdaptiveEvent : UseEvent Nat Bool Nat Bool Unit Nat :=
  { eventId := 4
    evidence := false
    round := 7
    role := .generate
    dependencies := {true}
    protocol := ()
    usedAt := 3 }

private def semanticOldLedger : RoleLedger Nat Bool Nat Bool Unit Nat :=
  { events := [semanticAdjudicateEvent]
    uniqueEventIds := by simp [semanticAdjudicateEvent]
    strictEventOrder := by simp
    indexRespectsRound := by
      intro event later inEvents inLater _before
      simp only [List.mem_singleton] at inEvents inLater
      subst event
      subst later
      exact le_rfl
    indexRespectsTime := by
      intro event later inEvents inLater _before
      simp only [List.mem_singleton] at inEvents inLater
      subst event
      subst later
      exact le_rfl }

private def semanticExtendedLedger : RoleLedger Nat Bool Nat Bool Unit Nat :=
  { events := [semanticAdjudicateEvent, semanticAdaptiveEvent]
    uniqueEventIds := by simp [semanticAdjudicateEvent, semanticAdaptiveEvent]
    strictEventOrder := by simp [semanticAdjudicateEvent, semanticAdaptiveEvent]
    indexRespectsRound := by
      intro event later inEvents inLater before
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inEvents inLater
      rcases inEvents with rfl | rfl <;> rcases inLater with rfl | rfl <;>
        simp [semanticAdjudicateEvent, semanticAdaptiveEvent] at before ⊢
    indexRespectsTime := by
      intro event later inEvents inLater before
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inEvents inLater
      rcases inEvents with rfl | rfl <;> rcases inLater with rfl | rfl <;>
        simp_all [semanticAdjudicateEvent, semanticAdaptiveEvent] }

private theorem semanticOldValid : ValidTrace semanticOldLedger semanticSnapshot := by
  intro event inLedger
  simp only [semanticOldLedger, List.mem_singleton] at inLedger
  subst event
  exact Or.inr ⟨rfl, by decide⟩

private theorem semanticExtendedValid :
    ValidTrace semanticExtendedLedger semanticSnapshot := by
  intro event inLedger
  simp only [semanticExtendedLedger, List.mem_cons, List.not_mem_nil, or_false] at inLedger
  rcases inLedger with rfl | rfl
  · exact Or.inr ⟨rfl, by decide⟩
  · exact Or.inr ⟨rfl, by decide⟩

private theorem semanticOldAdmissible :
    AdmissibleJudge semanticOldLedger semanticSnapshot semanticOldValid false := by
  unfold AdmissibleJudge
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨semanticAdjudicateEvent, ?_, rfl, rfl, rfl⟩
    simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
      RolePrefixAtTime, semanticOldLedger, semanticSnapshot, semanticAdjudicateEvent]
  · simp [semanticSnapshot, semanticFiltration]
  · simp [semanticSnapshot]
  · rintro ⟨event, inPrefix, _evidenceEq, adaptiveRole, _touches⟩
    have eventEq : event = semanticAdjudicateEvent := by
      simpa [semanticOldLedger, semanticAdjudicateEvent] using inPrefix.1.1
    subst event
    simp [adaptiveRoles, semanticAdjudicateEvent] at adaptiveRole

private theorem semanticAdaptiveUse :
    AdaptiveUseInClosure semanticExtendedLedger semanticSnapshot
      semanticExtendedValid false := by
  refine ⟨semanticAdaptiveEvent, ?_, rfl,
    by simp [semanticAdaptiveEvent, adaptiveRoles], ?_⟩
  · simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
      RolePrefixAtTime, semanticExtendedLedger, semanticSnapshot, semanticAdaptiveEvent]
  · refine ⟨true, by simp [semanticAdaptiveEvent], ?_⟩
    exact ⟨true, by simp [semanticSnapshot], Relation.ReflTransGen.refl⟩

private theorem semanticNewRejected :
    Not (AdmissibleJudge semanticExtendedLedger semanticSnapshot
      semanticExtendedValid false) := by
  intro admitted
  exact admitted.2.2.2 semanticAdaptiveUse

private theorem semanticAppendEquality :
    semanticExtendedLedger.events =
      semanticOldLedger.events ++ [semanticAdaptiveEvent] := by
  rfl

private theorem semanticEarlyEvent :
    semanticAdaptiveEvent.eventId <= semanticSnapshot.decisionEvent := by
  decide

private theorem semanticTouchesClosure :
    Set.Nonempty
      (semanticAdaptiveEvent.dependencies ∩ semanticSnapshot.dependencyClosure) := by
  refine ⟨true, by simp [semanticAdaptiveEvent], ?_⟩
  exact ⟨true, by simp [semanticSnapshot], Relation.ReflTransGen.refl⟩

theorem admissible_judge_early_append_witness :
    AdmissibleJudge semanticOldLedger semanticSnapshot semanticOldValid false /\
      Not (AdmissibleJudge semanticExtendedLedger semanticSnapshot
        semanticExtendedValid false) /\
      semanticExtendedLedger.events =
        semanticOldLedger.events ++ [semanticAdaptiveEvent] /\
      semanticAdaptiveEvent.eventId <= semanticSnapshot.decisionEvent /\
      Set.Nonempty
        (semanticAdaptiveEvent.dependencies ∩ semanticSnapshot.dependencyClosure) := by
  exact ⟨semanticOldAdmissible, semanticNewRejected, semanticAppendEquality,
    semanticEarlyEvent, semanticTouchesClosure⟩

#print axioms admissible_judge_early_append_witness

end D5.S3.ConceptDynamics.Provenance.SeenDirectionAndAppendCounterexample
