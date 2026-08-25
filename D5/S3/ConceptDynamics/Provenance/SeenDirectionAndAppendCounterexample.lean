/- GID: D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Direction witnesses for incoming closures and the strict late-append boundary. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation
import D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure

/- Library-search audit trail (2026-08-25):
   * `rg -n 'Relation\.ReflTransGen|Set \(.*x.*\)' \
       D5/S3/ConceptDynamics --glob '*.lean' | head -20`
     found the pinned reachability carrier and unrelated pair relations; no
     direction witness for DECT's evidence filtration was present.
   * `rg -n -i 'incoming|outgoing|predecessor|ancestor|dependency closure|'\
       'joint|common|shared|indexed|family|union|intersection|kernel|readout' \
       D5/S3/ConceptDynamics/Provenance --glob '*.lean' | head -40`
     found and reused `Contam`, `EvidenceFiltration.seen`, and
     `AdjudicationSnapshot.dependencyClosure`; no synonym is introduced here.
   * `git grep -n -E \
       '^def |^  def |^structure |^inductive |^abbrev |^theorem ' -- \
       D5/S3/ConceptDynamics/Provenance | head -60`
     found the role module's existing append-invariance theorem and no semantic
     early-append counterexample. This file adds only concrete witness objects.
   * `grep -rl \
       'RoleAdmissionContaminationClosure\|SeenDirectionAndAppendCounterexample' \
       Golden/Frozen/accepted/*.json`
     returned no paths, so neither module is frozen.
   * `nl -ba docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md | \
       sed -n '3609,3750p'`
     confirmed outgoing `Contam` at line 3728, incoming `Dep*` at line 3694,
     incoming access closure at line 3621, and the strict append condition at
     line 3721. Lines 3661 and 3714-3717 only consume those directed objects.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.SeenDirectionAndAppendCounterexample

open D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure

private def directionRelation : Bool -> Bool -> Prop :=
  fun source target => source = false /\ target = true

private def reverseDirectionRelation : Bool -> Bool -> Prop :=
  fun source target => source = true /\ target = false

private theorem direction_from_true_eq {target : Bool}
    (reachable : Relation.ReflTransGen directionRelation true target) :
    target = true := by
  induction reachable with
  | refl => rfl
  | tail _ step _ => exact step.2

private theorem reverse_from_false_eq {target : Bool}
    (reachable : Relation.ReflTransGen reverseDirectionRelation false target) :
    target = false := by
  induction reachable with
  | refl => rfl
  | tail _ step _ => exact step.2

theorem contam_direction_witness :
    true ∈ Contam directionRelation ({false} : Set Bool) /\
      false ∉ Contam directionRelation ({true} : Set Bool) := by
  constructor
  · exact ⟨false, by simp, Relation.ReflTransGen.single (by simp [directionRelation])⟩
  · rintro ⟨root, rootMem, reachable⟩
    have rootEq : root = true := by simpa using rootMem
    subst root
    exact Bool.noConfusion (direction_from_true_eq reachable)

private def directionFiltration : EvidenceFiltration Nat Bool :=
  { seen := fun cutoff =>
      {evidence | 0 < cutoff /\
        Relation.ReflTransGen directionRelation evidence true}
    monotone := by
      intro i j hij evidence seen
      exact ⟨seen.1.trans_le hij, seen.2⟩ }

private def directionSnapshot : AdjudicationSnapshot Nat Bool Nat Bool Nat 7 :=
  { freezeEvent := 1
    decisionEvent := 3
    frozenAt := 1
    decidedAt := 2
    freezeBeforeDecision := by decide
    timeBeforeDecision := by decide
    filtration := directionFiltration
    artifactDependsOn := directionRelation
    commitmentRoots := {true}
    evidenceDependsOn := directionRelation
    evidenceDependencies := {false}
    commitmentClosureVisibleAtFreeze := by
      intro evidence dependency
      have evidenceEq : evidence = false := by simpa using dependency
      subst evidence
      exact ⟨by decide,
        Relation.ReflTransGen.single (by simp [directionRelation])⟩ }

theorem dependency_closure_direction_witness :
    false ∈ directionSnapshot.dependencyClosure /\
      false ∈ directionSnapshot.evidenceDependencies /\
      false ∈ directionSnapshot.filtration.seen directionSnapshot.freezeEvent /\
      false ∉ Contam directionRelation directionSnapshot.commitmentRoots := by
  have artifactIncoming : false ∈ directionSnapshot.dependencyClosure := by
    refine ⟨true, by simp [directionSnapshot], ?_⟩
    exact Relation.ReflTransGen.single ⟨rfl, rfl⟩
  have evidenceIncoming : false ∈ directionSnapshot.evidenceDependencies := by
    simp [directionSnapshot]
  have visible :=
    directionSnapshot.commitmentClosureVisibleAtFreeze evidenceIncoming
  have notOutgoing : false ∉
      Contam directionRelation directionSnapshot.commitmentRoots := by
    rintro ⟨root, rootMem, reachable⟩
    have rootEq : root = true := by simpa [directionSnapshot] using rootMem
    subst root
    exact Bool.noConfusion (direction_from_true_eq reachable)
  exact ⟨artifactIncoming, evidenceIncoming, visible, notOutgoing⟩

private def seenForward : EvidenceFiltration Nat Bool :=
  directionFiltration

private def seenReverse : EvidenceFiltration Nat Bool :=
  { seen := fun cutoff =>
      {evidence | 0 < cutoff /\
        Relation.ReflTransGen reverseDirectionRelation evidence true}
    monotone := by
      intro i j hij evidence seen
      exact ⟨seen.1.trans_le hij, seen.2⟩ }

theorem seen_direction_witness :
    false ∈ seenForward.seen 1 /\
      false ∉ seenReverse.seen 1 /\
      false ∉ seenForward.seen 0 := by
  constructor
  · exact ⟨by decide,
      Relation.ReflTransGen.single (by simp [directionRelation])⟩
  constructor
  · rintro ⟨_positive, reachable⟩
    exact Bool.noConfusion (reverse_from_false_eq reachable)
  · rintro ⟨positive, _reachable⟩
    omega

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
    evidenceDependencies := {true}
    commitmentClosureVisibleAtFreeze := by
      intro evidence dependency
      have evidenceEq : evidence = true := by simpa using dependency
      subst evidence
      exact Or.inl ⟨rfl, le_rfl⟩ }

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

theorem admissible_judge_early_append_witness :
    AdmissibleJudge semanticOldLedger semanticSnapshot semanticOldValid false /\
      Not (AdmissibleJudge semanticExtendedLedger semanticSnapshot
        semanticExtendedValid false) /\
      semanticExtendedLedger.events =
        semanticOldLedger.events ++ [semanticAdaptiveEvent] /\
      semanticAdaptiveEvent.eventId <= semanticSnapshot.decisionEvent /\
      Set.Nonempty
        (semanticAdaptiveEvent.dependencies ∩ semanticSnapshot.dependencyClosure) := by
  refine ⟨semanticOldAdmissible, semanticNewRejected, rfl, by decide, ?_⟩
  refine ⟨true, by simp [semanticAdaptiveEvent], ?_⟩
  exact ⟨true, by simp [semanticSnapshot], Relation.ReflTransGen.refl⟩

theorem role_admission_direction_nonvacuity :
    (true ∈ Contam directionRelation ({false} : Set Bool) /\
      false ∉ Contam directionRelation ({true} : Set Bool)) /\
    (false ∈ directionSnapshot.dependencyClosure /\
      false ∈ directionSnapshot.evidenceDependencies /\
      false ∈ directionSnapshot.filtration.seen directionSnapshot.freezeEvent /\
      false ∉ Contam directionRelation directionSnapshot.commitmentRoots) /\
    (false ∈ seenForward.seen 1 /\
      false ∉ seenReverse.seen 1 /\
      false ∉ seenForward.seen 0) /\
    (AdmissibleJudge semanticOldLedger semanticSnapshot semanticOldValid false /\
      Not (AdmissibleJudge semanticExtendedLedger semanticSnapshot
        semanticExtendedValid false) /\
      semanticExtendedLedger.events =
        semanticOldLedger.events ++ [semanticAdaptiveEvent] /\
      semanticAdaptiveEvent.eventId <= semanticSnapshot.decisionEvent /\
      Set.Nonempty
        (semanticAdaptiveEvent.dependencies ∩ semanticSnapshot.dependencyClosure)) := by
  exact ⟨contam_direction_witness, dependency_closure_direction_witness,
    seen_direction_witness, admissible_judge_early_append_witness⟩

#print axioms contam_direction_witness
#print axioms dependency_closure_direction_witness
#print axioms seen_direction_witness
#print axioms admissible_judge_early_append_witness
#print axioms role_admission_direction_nonvacuity

end D5.S3.ConceptDynamics.Provenance.SeenDirectionAndAppendCounterexample
