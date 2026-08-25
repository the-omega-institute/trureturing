/- GID: D5/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/SeenDirectionAndAppendCounterexample
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Direction witnesses for dependency closures and an early-append admission counterexample. -/

import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation
import D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure

/- Library-search audit trail (2026-08-25):
   * `rg -n 'Relation\\.ReflTransGen|Set \\(.*×.*\\)' D5/S3/ConceptDynamics --glob '*.lean' | head -20`
     found the pinned reachability carrier and several unrelated pair relations; no
     direction witness for DECT's access filtration.
   * `rg -n -i 'incoming|outgoing|predecessor|ancestor|dependency closure|joint|common|shared|indexed|family|union|intersection|kernel|readout' D5/S3/ConceptDynamics/Provenance --glob '*.lean' | head -40`
     found the existing role module and finite proof-path semantics. No separate
     incoming `seen` witness or semantic early-append counterexample was present.
   * `git grep -n -E '^def |^  def |^structure |^inductive |^abbrev |^theorem ' -- D5/S3/ConceptDynamics/Provenance | head -60`
     found `Contam`, `EvidenceFiltration.seen`, `AdjudicationSnapshot.dependencyClosure`,
     and the existing append-invariance theorem; this file reuses those declarations.
   * `grep -rl 'RoleAdmissionContaminationClosure\\|SeenDirectionAndAppend' Golden/Frozen/accepted/*.json`
     returned no paths, so neither the corrected source module nor this witness module
     is frozen and no accepted descriptor is modified.
   * `docs/develop/theory/DEFINITION_ESCAPE_COMPLETION_THEORY.md:3621-3631` defines
     `seen` as the dependency closure of accessed objects and `FirstSeen` from that
     filtration; `:3691-3721` defines incoming commitment closure and the strict
     post-decision append condition. The constructions below instantiate only those
     source-defined objects on `Bool`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.SeenDirectionAndAppendCounterexample

open D5.S3.ConceptDynamics.Provenance.RoleAdmissionContaminationClosure

private def directionRelation : Bool → Bool → Prop :=
  fun source target ↦ source = false ∧ target = true

private def reverseDirectionRelation : Bool → Bool → Prop :=
  fun source target ↦ source = true ∧ target = false

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
    true ∈ Contam directionRelation ({false} : Set Bool) ∧
      false ∉ Contam directionRelation ({true} : Set Bool) := by
  constructor
  · exact ⟨false, by simp, Relation.ReflTransGen.single (by simp [directionRelation])⟩
  · rintro ⟨root, rootMem, reachable⟩
    have rootEq : root = true := by simpa using rootMem
    subst root
    exact Bool.noConfusion (direction_from_true_eq reachable)

private def directionFiltration : EvidenceFiltration Bool Nat :=
  { accessLedger := ⟨[.access true, .commitmentFreeze 7, .access false]⟩
    dependsOn := directionRelation }

private def directionSnapshot : AdjudicationSnapshot Bool Nat Nat 7 :=
  { freezeEvent := 1
    decisionEvent := 3
    frozenAt := 1
    decidedAt := 2
    freezeBeforeDecision := by decide
    timeBeforeDecision := by decide
    filtration := directionFiltration
    commitmentRoots := {true}
    freezeRecorded := rfl
    commitmentClosureVisibleAtFreeze := by
      intro object contaminated
      rcases contaminated with ⟨root, rootMem, reachable⟩
      have rootEq : root = true := by simpa using rootMem
      subst root
      have objectEq : object = true := direction_from_true_eq reachable
      subst object
      exact ⟨0, true, by decide, rfl, Relation.ReflTransGen.refl⟩ }

theorem dependency_closure_direction_witness :
    false ∈ directionSnapshot.dependencyClosure ∧
      false ∉ Contam directionRelation directionSnapshot.commitmentRoots := by
  constructor
  · refine ⟨true, by simp [directionSnapshot], ?_⟩
    exact Relation.ReflTransGen.single ⟨rfl, rfl⟩
  · rintro ⟨root, rootMem, reachable⟩
    have rootEq : root = true := by simpa [directionSnapshot] using rootMem
    subst root
    exact Bool.noConfusion (direction_from_true_eq reachable)

private def seenForward : EvidenceFiltration Bool Nat :=
  { accessLedger := ⟨[.access true]⟩
    dependsOn := directionRelation }

private def seenReverse : EvidenceFiltration Bool Nat :=
  { accessLedger := ⟨[.access true]⟩
    dependsOn := reverseDirectionRelation }

theorem seen_direction_witness :
    false ∈ seenForward.seen 1 ∧
      false ∉ seenReverse.seen 1 ∧
      false ∉ seenForward.seen 0 := by
  constructor
  · exact ⟨0, true, by decide, rfl,
      Relation.ReflTransGen.single (by simp [seenForward, directionRelation])⟩
  constructor
  · rintro ⟨index, accessed, before, atIndex, reachable⟩
    have indexEq : index = 0 := by omega
    subst index
    have accessedEq : accessed = true := by
      simpa [seenReverse] using atIndex.symm
    subst accessed
    exact Bool.noConfusion (reverse_from_false_eq reachable)
  · rintro ⟨index, _accessed, before, _atIndex, _reachable⟩
    omega

private def semanticFiltration : EvidenceFiltration Bool Nat :=
  { accessLedger := ⟨[.access true, .commitmentFreeze 7, .access false]⟩
    dependsOn := fun source target ↦ source = target }

private theorem semantic_reachable_eq {source target : Bool}
    (reachable : Relation.ReflTransGen semanticFiltration.dependsOn source target) :
    source = target := by
  change Relation.ReflTransGen (fun left right : Bool ↦ left = right) source target at reachable
  simpa only [Relation.reflTransGen_eq_self] using reachable

private def semanticSnapshot : AdjudicationSnapshot Bool Nat Nat 7 :=
  { freezeEvent := 1
    decisionEvent := 4
    frozenAt := 1
    decidedAt := 3
    freezeBeforeDecision := by decide
    timeBeforeDecision := by decide
    filtration := semanticFiltration
    commitmentRoots := {true}
    freezeRecorded := rfl
    commitmentClosureVisibleAtFreeze := by
      intro object contaminated
      rcases contaminated with ⟨root, rootMem, reachable⟩
      have rootEq : root = true := by simpa using rootMem
      subst root
      have objectEq : object = true := (semantic_reachable_eq reachable).symm
      subst object
      exact ⟨0, true, by decide, rfl, Relation.ReflTransGen.refl⟩ }

private def semanticAdjudicateEvent : UseEvent Bool Nat Unit Nat :=
  { eventId := 3
    evidence := false
    round := 7
    role := .adjudicate
    dependencies := ∅
    protocol := ()
    usedAt := 2 }

private def semanticAdaptiveEvent : UseEvent Bool Nat Unit Nat :=
  { eventId := 4
    evidence := false
    round := 7
    role := .generate
    dependencies := {true}
    protocol := ()
    usedAt := 3 }

private def semanticOldLedger : RoleLedger Bool Nat Unit Nat :=
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

private def semanticExtendedLedger : RoleLedger Bool Nat Unit Nat :=
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
  exact ⟨2, false, by decide, rfl, Relation.ReflTransGen.refl⟩

private theorem semanticExtendedValid : ValidTrace semanticExtendedLedger semanticSnapshot := by
  intro event inLedger
  simp only [semanticExtendedLedger, List.mem_cons, List.not_mem_nil, or_false] at inLedger
  rcases inLedger with rfl | rfl
  · exact ⟨2, false, by decide, rfl, Relation.ReflTransGen.refl⟩
  · exact ⟨2, false, by decide, rfl, Relation.ReflTransGen.refl⟩

private theorem semanticOldAdmissible :
    AdmissibleJudge semanticOldLedger semanticSnapshot semanticOldValid false := by
  unfold AdmissibleJudge
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨semanticAdjudicateEvent, ?_, rfl, rfl, rfl⟩
    simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
      RolePrefixAtTime, semanticOldLedger, semanticSnapshot, semanticAdjudicateEvent]
  · rw [freeze_lt_first_seen_iff]
    intro index before seen
    rcases seen with ⟨accessIndex, accessed, accessBefore, atIndex, reachable⟩
    change index ≤ 1 at before
    have accessIndexEq : accessIndex = 0 := by omega
    have indexEq : index = 1 := by omega
    subst accessIndex
    subst index
    have accessedEq : accessed = true := by
      simpa [semanticSnapshot, semanticFiltration] using atIndex.symm
    subst accessed
    exact Bool.noConfusion (semantic_reachable_eq reachable)
  · rintro ⟨root, rootMem, reachable⟩
    have rootEq : root = true := by simpa [semanticSnapshot] using rootMem
    subst root
    exact Bool.noConfusion (semantic_reachable_eq reachable)
  · rintro ⟨event, inPrefix, _evidenceEq, adaptiveRole, _touches⟩
    have eventEq : event = semanticAdjudicateEvent := by
      simpa [semanticOldLedger, semanticAdjudicateEvent] using inPrefix.1.1
    subst event
    simp [adaptiveRoles, semanticAdjudicateEvent] at adaptiveRole

private theorem semanticAdaptiveUse :
    AdaptiveUseInClosure semanticExtendedLedger semanticSnapshot semanticExtendedValid false := by
  refine ⟨semanticAdaptiveEvent, ?_, rfl,
    by simp [semanticAdaptiveEvent, adaptiveRoles], ?_⟩
  · simp [InAdjudicationPrefix, RolePrefixAtEvent, RolePrefixAtRound,
      RolePrefixAtTime, semanticExtendedLedger, semanticSnapshot, semanticAdaptiveEvent]
  · refine ⟨true, ?_⟩
    constructor
    · simp [semanticAdaptiveEvent]
    · exact ⟨true, by simp [semanticSnapshot], Relation.ReflTransGen.refl⟩

private theorem semanticNewRejected :
    ¬ AdmissibleJudge semanticExtendedLedger semanticSnapshot semanticExtendedValid false := by
  intro admitted
  exact admitted.2.2.2 semanticAdaptiveUse

theorem admissible_judge_early_append_witness :
    AdmissibleJudge semanticOldLedger semanticSnapshot semanticOldValid false ∧
      ¬ AdmissibleJudge semanticExtendedLedger semanticSnapshot semanticExtendedValid false ∧
      semanticExtendedLedger.events =
        semanticOldLedger.events ++ [semanticAdaptiveEvent] ∧
      semanticAdaptiveEvent.eventId ≤ semanticSnapshot.decisionEvent ∧
      Set.Nonempty
        (semanticAdaptiveEvent.dependencies ∩ semanticSnapshot.dependencyClosure) := by
  refine ⟨semanticOldAdmissible, semanticNewRejected, rfl, by decide, ?_⟩
  refine ⟨true, ?_⟩
  constructor
  · simp [semanticAdaptiveEvent]
  · exact ⟨true, by simp [semanticSnapshot], Relation.ReflTransGen.refl⟩

theorem role_admission_direction_nonvacuity :
    (true ∈ Contam directionRelation ({false} : Set Bool) ∧
      false ∉ Contam directionRelation ({true} : Set Bool)) ∧
    (false ∈ directionSnapshot.dependencyClosure ∧
      false ∉ Contam directionRelation directionSnapshot.commitmentRoots) ∧
    (false ∈ seenForward.seen 1 ∧
      false ∉ seenReverse.seen 1 ∧
      false ∉ seenForward.seen 0) ∧
    (AdmissibleJudge semanticOldLedger semanticSnapshot semanticOldValid false ∧
      ¬ AdmissibleJudge semanticExtendedLedger semanticSnapshot semanticExtendedValid false ∧
      semanticExtendedLedger.events =
        semanticOldLedger.events ++ [semanticAdaptiveEvent] ∧
      semanticAdaptiveEvent.eventId ≤ semanticSnapshot.decisionEvent ∧
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
