/- GID: D5/S3/ConceptDynamics/Dependency/BasicDependencyRules
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Dependency/BasicDependencyRules
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Factorization dependence obeys reflexivity, join, and composition rules. -/

import D5.S3.ConceptDynamics.Refinement.RefinementTransitivity

/- Library-search audit trail (2026-08-23):
   * Repository searches found the canonical `Concept`, `Refines`, and
     `conceptJoin` definitions and the exact projection and merge clauses in
     `concept_join_universal`; those declarations are imported and applied.
   * The exact composition clause is already supplied by
     `refinement_transitive` and is applied directly.
   * No repository declaration or digestion receipt packages reflexivity,
     projection, transitivity, augmentation, merge, decomposition, and
     pseudotransitivity in one public statement.
   * Pinned Mathlib contains `Function.FactorsThrough` and its composition API.
     The repository's `Refines` is the canonical family relation, so no parallel
     dependency predicate is introduced. `Function.DependsOn` concerns selected
     product coordinates and is not the source relation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Dependency.BasicDependencyRules

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.RefinementTransitivity

/-- Concept dependence by factorization satisfies all seven basic rules. -/
theorem basic_dependency_rules
    {X A B C D : Type*}
    (q_A : Concept X A) (q_B : Concept X B)
    (q_C : Concept X C) (q_D : Concept X D) :
    Refines q_A q_A ∧
      (Refines q_A (conceptJoin q_A q_B) ∧
        Refines q_B (conceptJoin q_A q_B)) ∧
      (Refines q_B q_A → Refines q_C q_B → Refines q_C q_A) ∧
      (Refines q_B q_A →
        Refines (conceptJoin q_B q_C) (conceptJoin q_A q_C)) ∧
      (Refines q_B q_A → Refines q_C q_A →
        Refines (conceptJoin q_B q_C) q_A) ∧
      (Refines (conceptJoin q_B q_C) q_A →
        Refines q_B q_A ∧ Refines q_C q_A) ∧
      (Refines q_B q_A → Refines q_D (conceptJoin q_B q_C) →
        Refines q_D (conceptJoin q_A q_C)) := by
  constructor
  · exact ⟨id, rfl⟩
  constructor
  · exact ⟨
      (concept_join_universal q_A q_B (conceptJoin q_A q_B)).1,
      (concept_join_universal q_A q_B (conceptJoin q_A q_B)).2.1⟩
  constructor
  · intro hAB hBC
    exact refinement_transitive q_C q_B q_A hAB hBC
  constructor
  · rintro ⟨factor, hfactor⟩
    refine ⟨fun pair => (factor pair.1, pair.2), ?_⟩
    funext x
    change (q_B x, q_C x) = (factor (q_A x), q_C x)
    rw [hfactor]
    rfl
  constructor
  · intro hAB hAC
    exact (concept_join_universal q_B q_C q_A).2.2 hAB hAC
  constructor
  · intro hJoin
    exact ⟨
      refinement_transitive q_B (conceptJoin q_B q_C) q_A hJoin
        (concept_join_universal q_B q_C (conceptJoin q_B q_C)).1,
      refinement_transitive q_C (conceptJoin q_B q_C) q_A hJoin
        (concept_join_universal q_B q_C (conceptJoin q_B q_C)).2.1⟩
  · rintro ⟨factor, hfactor⟩ hD
    have hAugmented :
        Refines (conceptJoin q_B q_C) (conceptJoin q_A q_C) := by
      refine ⟨fun pair => (factor pair.1, pair.2), ?_⟩
      funext x
      change (q_B x, q_C x) = (factor (q_A x), q_C x)
      rw [hfactor]
      rfl
    exact refinement_transitive q_D (conceptJoin q_B q_C)
      (conceptJoin q_A q_C) hAugmented hD

#print axioms basic_dependency_rules

end D5.S3.ConceptDynamics.Dependency.BasicDependencyRules
