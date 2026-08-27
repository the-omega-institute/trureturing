/- GID: D5/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureZeroGainCriterion
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeLaws/SemanticClosureZeroGainCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Semantic redundancy is exactly preservation of the common kernel. -/

import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

/- Library-search audit trail (2026-08-28):
   * The frozen `DefinitionKernelGalois` module supplies the canonical `SemanticClosure`,
     `jointKernel`, and `mem_semanticClosure_iff_fiber_constant` declarations. No parallel
     closure, kernel, or readout carrier is introduced here.
   * Repository searches found no theorem equating the common kernel after inserting one
     candidate with the original kernel. The pinned Mathlib search found `Set.mem_insert_iff`,
     `Set.mem_iInter`, and `Set.Subset.antisymm`, which are applied below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

/- A candidate belongs to the semantic closure of a readout family exactly when adding that
candidate leaves the family's common observational kernel unchanged. -/
theorem semantic_closure_zero_gain_criterion
    {X Output : Type*}
    (Gamma : Set (Concept X Output)) (candidate : Concept X Output) :
    candidate ∈ SemanticClosure Gamma ↔
      jointKernel
          (fun definition : Set.insert candidate Gamma => definition.1) =
        jointKernel (fun definition : Gamma => definition.1) := by
  constructor
  · intro invariant
    apply Set.Subset.antisymm
    · exact jointKernel_antitone (Set.subset_insert candidate Gamma)
    · intro pair pairInKernel
      apply Set.mem_iInter.2
      intro definition
      rcases definition with ⟨definition, definitionInInsert⟩
      rcases Set.mem_insert_iff.mp definitionInInsert with definitionEq | definitionInGamma
      · subst definition
        change candidate pair.1 = candidate pair.2
        exact invariant pairInKernel
      · exact Set.mem_iInter.1 pairInKernel ⟨definition, definitionInGamma⟩
  · intro unchanged
    apply (mem_semanticClosure_iff_fiber_constant Gamma candidate).2
    intro left right allEqual
    have pairInKernel :
        (left, right) ∈
          jointKernel (fun definition : Gamma => definition.1) := by
      apply Set.mem_iInter.2
      intro definition
      change definition.1 left = definition.1 right
      exact allEqual definition
    have pairInExtendedKernel :
        (left, right) ∈
          jointKernel
            (fun definition : Set.insert candidate Gamma => definition.1) := by
      rw [unchanged]
      exact pairInKernel
    have candidateEqual := Set.mem_iInter.1 pairInExtendedKernel
      (⟨candidate, Set.mem_insert_iff.mpr (Or.inl rfl)⟩ : Set.insert candidate Gamma)
    change candidate left = candidate right at candidateEqual
    exact candidateEqual

/- Negation is semantically redundant for the Boolean identity readout. -/
example :
    let Gamma : Set (Concept Bool Bool) := {fun x => x}
    let candidate : Concept Bool Bool := fun x => !x
    candidate ∈ SemanticClosure Gamma ↔
      jointKernel
          (fun definition : Set.insert candidate Gamma => definition.1) =
        jointKernel (fun definition : Gamma => definition.1) := by
  exact semantic_closure_zero_gain_criterion
    ({fun x : Bool => x} : Set (Concept Bool Bool)) (fun x => !x)

#print axioms semantic_closure_zero_gain_criterion

end D5.S3.ConceptDynamics.DefinitionEscapeLaws.SemanticClosureZeroGainCriterion
