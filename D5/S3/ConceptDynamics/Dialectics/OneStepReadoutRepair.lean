/- GID: D5/S3/ConceptDynamics/Dialectics/OneStepReadoutRepair
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dialectics/OneStepReadoutRepair
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical least joint interface for current and next readouts with supplied factors. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-25):
   * Shape searches for paired readouts and factorization in the current D5 tree
     found the canonical `Concept`, `Refines`, and `conceptJoin` primitives and
     the frozen theorem `concept_join_universal`; they are imported and applied.
   * `MinimalDialecticalRepair.minimal_dialectical_repair` and
     `LeastCommonReadoutRefinement.least_common_readout_refinement` expose the
     adjacent universal refinement property, but neither publicly states the
     equality assembled from the particular supplied component factors.
   * Pinned Mathlib searches found generic product and function-composition
     infrastructure but no exact current/next-readout theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dialectics.OneStepReadoutRepair

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

/-- The joint interface of the current and next readouts preserves both and is
coarsest: any supplied factors through another interface assemble to the stated
factorization of the canonical joint readout. -/
theorem one_step_readout_repair
    {X B : Type _} (q : Concept X B) (F : X -> X) :
    Refines q (conceptJoin q (q ∘ F)) /\
      Refines (q ∘ F) (conceptJoin q (q ∘ F)) /\
      forall {C : Type _} (r : Concept X C) (a b : C -> B),
        q = a ∘ r ->
          q ∘ F = b ∘ r ->
            conceptJoin q (q ∘ F) = (fun c => (a c, b c)) ∘ r := by
  refine ⟨
    (concept_join_universal q (q ∘ F) (conceptJoin q (q ∘ F))).1,
    (concept_join_universal q (q ∘ F) (conceptJoin q (q ∘ F))).2.1,
    ?_⟩
  intro C r a b hcurrent hnext
  funext x
  change (q x, (q ∘ F) x) = (a (r x), b (r x))
  rw [congrFun hcurrent x, congrFun hnext x]
  rfl

#print axioms one_step_readout_repair

end D5.S3.ConceptDynamics.Dialectics.OneStepReadoutRepair
