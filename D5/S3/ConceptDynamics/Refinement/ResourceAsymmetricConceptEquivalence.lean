/- GID: D5/S3/ConceptDynamics/Refinement/ResourceAsymmetricConceptEquivalence
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/ResourceAsymmetricConceptEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite permutation can be concept-equivalent but resource-asymmetric. -/

import D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
import D5.S3.ConceptDynamics.Refinement.ResourceRefinementComposition

/- Library-search audit trail (2026-08-22):
   * Exact family hits `ConceptEquivalent`, `ResourceCost`, and `ResourceRefines`
     are imported and used directly rather than redeclared.
   * Exact pinned-Mathlib hits `Equiv.Perm`, `Equiv.symm_apply_apply`, and
     `Equiv.apply_symm_apply` provide the source bijection and inverse laws.
   * Searches for ordinary concept equivalence with one-way bounded recovery
     found no theorem containing both the positive and negative resource clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.ResourceAsymmetricConceptEquivalence

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Interventions.RedundantAppealDefectPersistence
open D5.S3.ConceptDynamics.Refinement.ResourceRefinementComposition

universe u

/-- The identity readout and a finite permutation are ordinarily equivalent.
When the permutation is within budget but its inverse is not, resource
refinement holds only from the identity readout to the permuted readout. -/
theorem ordinary_equivalence_does_not_imply_resource_equivalence
    {X : Type u} [Finite X]
    (permutation : Equiv.Perm X)
    (cost : ResourceCost) (budget : Nat)
    (costAsymmetry :
      cost (permutation : X -> X) ≤ budget ∧
        ¬cost (permutation.symm : X -> X) ≤ budget) :
    ConceptEquivalent
        (id : Concept X X) (permutation : X -> X) ∧
      ResourceRefines cost budget
        (permutation : X -> X) (id : Concept X X) ∧
      ¬ResourceRefines cost budget
        (id : Concept X X) (permutation : X -> X) := by
  constructor
  · constructor
    · refine ⟨permutation.symm, ?_⟩
      funext state
      exact (permutation.symm_apply_apply state).symm
    · exact ⟨permutation, rfl⟩
  constructor
  · exact ⟨permutation, rfl, costAsymmetry.1⟩
  · rintro ⟨factor, hfactor, factorWithinBudget⟩
    apply costAsymmetry.2
    have factor_eq_inverse : factor = permutation.symm := by
      funext value
      have pointwise := congrFun hfactor (permutation.symm value)
      change permutation.symm value =
        factor (permutation (permutation.symm value)) at pointwise
      rw [permutation.apply_symm_apply] at pointwise
      exact pointwise.symm
    rw [factor_eq_inverse] at factorWithinBudget
    exact factorWithinBudget

/-- The public result specializes without changing either resource direction. -/
example {X : Type u} [Finite X]
    (permutation : Equiv.Perm X)
    (cost : ResourceCost) (budget : Nat)
    (costAsymmetry :
      cost (permutation : X -> X) ≤ budget ∧
        ¬cost (permutation.symm : X -> X) ≤ budget) :
    ResourceRefines cost budget
        (permutation : X -> X) (id : Concept X X) ∧
      ¬ResourceRefines cost budget
        (id : Concept X X) (permutation : X -> X) := by
  exact (ordinary_equivalence_does_not_imply_resource_equivalence
    permutation cost budget costAsymmetry).2

#print axioms ordinary_equivalence_does_not_imply_resource_equivalence

end D5.S3.ConceptDynamics.Refinement.ResourceAsymmetricConceptEquivalence
