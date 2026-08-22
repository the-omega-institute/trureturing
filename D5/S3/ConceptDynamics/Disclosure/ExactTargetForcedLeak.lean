/- GID: D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact target realization forces disclosure of its sensitive common part. -/

import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
import D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'exact_target_forced_leak' D5 Golden/Frozen/accepted` found no
     repository declaration or accepted duplicate.
   * The required repository search for `leak|Leak|sensitive|disclosure` found
     `InformedDisclosureDefect`, which concerns disclosure collisions and failed
     recovery, not refinement-monotone sensitive common parts.
   * `HistorySensitiveOutcomeReductionObstruction` concerns path-dependent
     evaluations, while `ProvenanceAdmissionCountermodel` concerns provenance;
     direct inspection confirmed that neither overlaps this theorem.
   * Exact family hits `Concept`, `Refines`, `conceptJoin`,
     `concept_join_universal`, `refinement_transitive`, and `ConceptEquivalent`
     are imported and reused. Searches found no concept-meet universal-property
     declaration, so only that predicate is defined locally.
   * Pinned Mathlib searches found `Function.FactorsThrough.extend_comp`, but no
     `IsGLB` or meet theorem for factorization; the family transitivity theorem
     above is the exact reusable interface. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence

universe u v

/-- A readout is the common part of two concepts when it is their greatest
lower bound in the factorization refinement order. -/
structure IsConceptMeet {X : Type u} {A B K : Type v}
    (left : Concept X A) (right : Concept X B) (meet : Concept X K) : Prop where
  refinesLeft : Refines meet left
  refinesRight : Refines meet right
  greatest {L : Type v} (lower : Concept X L) :
    Refines lower left -> Refines lower right -> Refines lower meet

/-- Definition 217.1: adding a concept creates no structural leak when the
post-addition and prior sensitive common parts have equal distinction power. -/
def StructurallyNoNewLeak
    {X : Type u} {P M S Before After : Type v}
    (publicConcept : Concept X P) (added : Concept X M) (sensitive : Concept X S)
    (before : Concept X Before) (after : Concept X After) : Prop :=
  IsConceptMeet publicConcept sensitive before ∧
    IsConceptMeet (conceptJoin publicConcept added) sensitive after ∧
    ConceptEquivalent after before

/-- Exact realization of a target forces its sensitive common part below the
leak common to the augmented public concept and the sensitive concept. -/
theorem exact_target_forced_leak
    {X : Type u} {P M S E K L : Type v}
    (publicConcept : Concept X P) (added : Concept X M) (sensitive : Concept X S)
    (target : Concept X E) (forcedPart : Concept X K) (leak : Concept X L)
    (targetRealized : Refines target (conceptJoin publicConcept added))
    (forcedPartIsMeet : IsConceptMeet target sensitive forcedPart)
    (leakIsMeet : IsConceptMeet (conceptJoin publicConcept added) sensitive leak) :
    Refines forcedPart leak := by
  apply leakIsMeet.greatest forcedPart
  · exact refinement_transitive forcedPart target (conceptJoin publicConcept added)
      targetRealized forcedPartIsMeet.refinesLeft
  · exact forcedPartIsMeet.refinesRight

/-- If adding information creates no structural leak, the target-forced
sensitive part already factors through the leak present in public information. -/
theorem forced_leak_preexists_of_structurally_no_new_leak
    {X : Type u} {P M S E K Before After : Type v}
    (publicConcept : Concept X P) (added : Concept X M) (sensitive : Concept X S)
    (target : Concept X E) (forcedPart : Concept X K)
    (before : Concept X Before) (after : Concept X After)
    (targetRealized : Refines target (conceptJoin publicConcept added))
    (forcedPartIsMeet : IsConceptMeet target sensitive forcedPart)
    (noNewLeak :
      StructurallyNoNewLeak publicConcept added sensitive before after) :
    Refines forcedPart before := by
  have forcedPartRefinesAfter : Refines forcedPart after :=
    exact_target_forced_leak publicConcept added sensitive target forcedPart after
      targetRealized forcedPartIsMeet noNewLeak.2.1
  exact refinement_transitive forcedPart after before noNewLeak.2.2.1
    forcedPartRefinesAfter

/-- Two Boolean coordinates give a finite instance where the target is exactly
realized and its forced sensitive part distinguishes two states. -/
theorem exact_target_forced_leak_nontrivial_witness :
    let publicConcept : Concept (Bool × Bool) Bool := Prod.fst
    let added : Concept (Bool × Bool) Bool := Prod.snd
    let sensitive : Concept (Bool × Bool) Bool := Prod.snd
    let target : Concept (Bool × Bool) Bool := Prod.snd
    let forcedPart : Concept (Bool × Bool) Bool := Prod.snd
    let leak : Concept (Bool × Bool) Bool := Prod.snd
    Refines target (conceptJoin publicConcept added) ∧
      IsConceptMeet target sensitive forcedPart ∧
      IsConceptMeet (conceptJoin publicConcept added) sensitive leak ∧
      Refines forcedPart leak ∧
      ∃ x y, forcedPart x ≠ forcedPart y := by
  dsimp
  refine ⟨⟨Prod.snd, rfl⟩, ?_, ?_, ⟨id, rfl⟩, ?_⟩
  · refine ⟨⟨id, rfl⟩, ⟨id, rfl⟩, ?_⟩
    intro L lower lowerRefinesTarget _
    exact lowerRefinesTarget
  · refine ⟨⟨Prod.snd, rfl⟩, ⟨id, rfl⟩, ?_⟩
    intro L lower _ lowerRefinesSensitive
    exact lowerRefinesSensitive
  · exact ⟨(false, false), (false, true), Bool.false_ne_true⟩

example :
    Refines (fun x : Bool × Bool => x.2)
      (conceptJoin (fun x : Bool × Bool => x.1) (fun x => x.2)) := by
  exact ⟨Prod.snd, rfl⟩

#print axioms exact_target_forced_leak

end D5.S3.ConceptDynamics.Disclosure.ExactTargetForcedLeak
