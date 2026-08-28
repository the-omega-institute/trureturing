/- GID: D5/S3/ConceptDynamics/DefinitionEscapeLaws/StrictKernelNoveltyCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeLaws/StrictKernelNoveltyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A candidate is semantically novel exactly when it strictly shrinks the common kernel. -/

import D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion

/- Library-search audit trail (2026-08-28):
   * Exact current-tree hit
     `SemanticClosureZeroGainCriterion.semantic_closure_zero_gain_criterion` states that
     closure membership is equivalent to equality of the inserted and original kernels.
     It is applied directly below.
   * Exact current-tree hit `DefinitionKernelGalois.jointKernel_antitone` supplies the
     inclusion from the inserted-family kernel into the original-family kernel.
   * Pinned Mathlib supplies `Set.ssubset_iff_subset_ne`; no separate strict-novelty
     theorem over the repository's canonical concept and semantic-closure carriers was found.
   * Body-shape searches for strict semantic closure, inserted joint kernels, and novelty
     found no exact owner beyond the equality criterion above. No new definition is added. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeLaws.StrictKernelNoveltyCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
open D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion

/-- Adding a candidate strictly shrinks the family's common observational kernel exactly
when that candidate lies outside the semantic closure of the original family. -/
theorem strict_kernel_novelty_criterion
    {X Output : Type*}
    (Gamma : Set (Concept X Output)) (candidate : Concept X Output) :
    jointKernel
        (fun definition : Set.insert candidate Gamma => definition.1) ⊂
      jointKernel (fun definition : Gamma => definition.1) ↔
        candidate ∉ SemanticClosure Gamma := by
  classical
  have kernelSubset :
      jointKernel
          (fun definition : Set.insert candidate Gamma => definition.1) ⊆
        jointKernel (fun definition : Gamma => definition.1) :=
    jointKernel_antitone (Set.subset_insert candidate Gamma)
  by_cases candidateInClosure : candidate ∈ SemanticClosure Gamma
  · have kernelsEqual :=
      (semantic_closure_zero_gain_criterion Gamma candidate).1 candidateInClosure
    constructor
    · intro strictKernel
      exact fun _ =>
        (Set.ssubset_iff_subset_ne.mp strictKernel).2 kernelsEqual
    · intro candidateOutsideClosure
      exact (candidateOutsideClosure candidateInClosure).elim
  · constructor
    · intro _
      exact candidateInClosure
    · intro _
      apply Set.ssubset_iff_subset_ne.mpr
      refine ⟨kernelSubset, ?_⟩
      intro kernelsEqual
      exact candidateInClosure
        ((semantic_closure_zero_gain_criterion Gamma candidate).2 kernelsEqual)

/- The identity readout strictly refines the empty family on Bool. -/
example :
    jointKernel
        (fun definition : Set.insert (fun x : Bool => x) ∅ => definition.1) ⊂
      jointKernel (fun definition : (∅ : Set (Concept Bool Bool)) => definition.1) ↔
        (fun x : Bool => x) ∉
          SemanticClosure (∅ : Set (Concept Bool Bool)) := by
  exact strict_kernel_novelty_criterion
    (∅ : Set (Concept Bool Bool)) (fun x => x)

#print axioms strict_kernel_novelty_criterion

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.StrictKernelNoveltyCriterion
