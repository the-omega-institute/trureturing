/- GID: D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureStrictNoveltyCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureStrictNoveltyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict kernel refinement is exactly escape from semantic closure. -/

import D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion

/- Library-search audit trail (2026-08-28):
   * The frozen zero-gain owner supplies the canonical `SemanticClosure`,
     `jointKernel`, and equality criterion; no sibling carrier is introduced.
   * Pinned Mathlib supplies `Set.ssubset_iff_of_subset` for strict inclusion.
   * Repository and Mathlib searches found no exact strict-novelty theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureStrictNoveltyCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion

/-- Adding a candidate strictly shrinks the old common kernel exactly when the
candidate lies outside the semantic closure of the old family. -/
theorem semantic_closure_strict_novelty_criterion
    {X Output : Type*}
    (Gamma : Set (Concept X Output)) (candidate : Concept X Output) :
    jointKernel
          (fun definition : Set.insert candidate Gamma => definition.1) ⊂
        jointKernel (fun definition : Gamma => definition.1) ↔
      candidate ∉ SemanticClosure Gamma := by
  have kernelSubset :
      jointKernel
          (fun definition : Set.insert candidate Gamma => definition.1) ⊆
        jointKernel (fun definition : Gamma => definition.1) :=
    jointKernel_antitone (Set.subset_insert candidate Gamma)
  constructor
  · intro strict outsideFailure
    exact strict.ne
      ((semantic_closure_zero_gain_criterion Gamma candidate).1 outsideFailure)
  · intro outside
    exact kernelSubset.ssubset_of_ne (fun kernelsEqual =>
      outside
        ((semantic_closure_zero_gain_criterion Gamma candidate).2 kernelsEqual))

#print axioms semantic_closure_strict_novelty_criterion

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureStrictNoveltyCriterion
