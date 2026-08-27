/- GID: D5/S3/ConceptDynamics/Completion/TargetFamilyCompletionMinimality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Completion/TargetFamilyCompletionMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adjoining an entire target family is the coarsest jointly sufficient refinement. -/

import D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency

/- Library-search audit trail (2026-08-28):
   * Exact repository primitives `Concept`, `Refines`, `conceptJoin`, and
     `jointTarget` construct the source completion directly; body-shape searches
     found these owners, so no parallel completion definition is introduced.
   * `multi_target_minimal_sufficiency` proves target-family minimality without
     adjoining the current interface, while
     `target_closure_is_least_target_sufficient_refinement` handles one target.
     Neither is an exact whole-theorem hit for `conceptJoin q (jointTarget targets)`.
   * Pinned Mathlib has no theorem packaging this concept-factorization order.
     The proof applies the two exact repository universal properties directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Completion.TargetFamilyCompletionMinimality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency

universe u v w z

/-- The completion obtained by adjoining every target value refines the current
interface, decides every target, and is coarsest among all interfaces having both
properties. Knowledge, prediction, causal, sequential-effect, indexed-readout,
strategy, and self-relevant completions are instances obtained by choosing the
corresponding target family. -/
theorem target_family_completion_is_coarsest
    {X : Type u} {I : Type v} {Y : I -> Type w} {Q : Type z}
    (q : Concept X Q) (targets : forall index, Concept X (Y index)) :
    Refines q (conceptJoin q (jointTarget targets)) ∧
      (forall index,
        Refines (targets index) (conceptJoin q (jointTarget targets))) ∧
      forall {D : Type*} (candidate : Concept X D),
        Refines q candidate ->
          (forall index, Refines (targets index) candidate) ->
            Refines (conceptJoin q (jointTarget targets)) candidate := by
  have joinLaws :=
    concept_join_universal q (jointTarget targets)
      (conceptJoin q (jointTarget targets))
  refine ⟨joinLaws.1, ?_, ?_⟩
  · exact
      (multi_target_minimal_sufficiency targets
        (conceptJoin q (jointTarget targets))).1.mpr joinLaws.2.1
  · intro D candidate refinesCurrent decidesTargets
    have decidesJoint : Refines (jointTarget targets) candidate :=
      (multi_target_minimal_sufficiency targets candidate).1.mp decidesTargets
    exact
      (concept_join_universal q (jointTarget targets) candidate).2.2
        refinesCurrent decidesJoint

#print axioms target_family_completion_is_coarsest

end D5.S3.ConceptDynamics.Completion.TargetFamilyCompletionMinimality
