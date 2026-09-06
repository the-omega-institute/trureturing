/- GID: D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative complements expose the exact boundaries of a set-valued model of naming Dao. -/

import D5.S3.ConceptDynamics.Negation.RelativeComplement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Negation.DaoConceptBoundarySpecialization

/-- A concept is a proper part of its horizon exactly when it is contained in
the horizon and leaves a nonempty relative remainder. -/
theorem concept_boundary_iff_nonempty_remainder
    {X : Type*} (horizon concept : Set X) :
    concept ⊂ horizon ↔
      concept ⊆ horizon ∧ (horizon \ concept).Nonempty := by
  constructor
  · intro strict
    rcases Set.ssubset_iff_exists.mp strict with
      ⟨inside, x, xInHorizon, xOutsideConcept⟩
    exact ⟨inside, x, xInHorizon, xOutsideConcept⟩
  · rintro ⟨inside, x, xInHorizon, xOutsideConcept⟩
    exact Set.ssubset_iff_exists.mpr
      ⟨inside, x, xInHorizon, xOutsideConcept⟩

/-- A relative opposite is a proper part of the horizon exactly when the
concept actually occupies some point of that horizon. -/
theorem relative_opposite_is_proper_iff_concept_present
    {X : Type*} (horizon concept : Set X) :
    horizon \ concept ⊂ horizon ↔ (horizon ∩ concept).Nonempty := by
  exact Set.sdiff_ssubset_left_iff

/-- A concept contained in its horizon and its relative opposite jointly
cover that horizon. -/
theorem relative_opposite_and_concept_cover_horizon
    {X : Type*} {horizon concept : Set X}
    (inside : concept ⊆ horizon) :
    (horizon \ concept) ∪ concept = horizon := by
  exact Set.sdiff_union_of_subset inside

/-- Relative complementation within one horizon distinguishes concepts that
are both contained in that horizon. -/
theorem equal_relative_opposites_iff_equal_concepts
    {X : Type*} {horizon first second : Set X}
    (firstInside : first ⊆ horizon)
    (secondInside : second ⊆ horizon) :
    horizon \ first = horizon \ second ↔ first = second := by
  exact sdiff_right_inj firstInside secondInside

/-- If every admissible expression is internal to a horizon and leaves a
nonempty remainder, no expression exhausts that horizon. -/
theorem admissible_expressions_are_proper_parts
    {X Expression : Type*}
    (horizon : Set X) (meaning : Expression → Set X)
    (inside : ∀ expression, meaning expression ⊆ horizon)
    (leavesRemainder :
      ∀ expression, (horizon \ meaning expression).Nonempty) :
    ∀ expression, meaning expression ⊂ horizon := by
  intro expression
  exact (concept_boundary_iff_nonempty_remainder
    horizon (meaning expression)).mpr
      ⟨inside expression, leavesRemainder expression⟩

/-- The expression called "Dao" is subject to the same non-exhaustion result
when it belongs to the quantified expression class. -/
theorem dao_name_is_a_proper_part_under_the_same_premises
    {X Expression : Type*}
    (horizon : Set X) (meaning : Expression → Set X)
    (daoName : Expression)
    (inside : ∀ expression, meaning expression ⊆ horizon)
    (leavesRemainder :
      ∀ expression, (horizon \ meaning expression).Nonempty) :
    meaning daoName ⊂ horizon := by
  exact admissible_expressions_are_proper_parts
    horizon meaning inside leavesRemainder daoName

/-- Boundary case: the relative opposite of an empty concept is the whole
horizon. -/
theorem empty_concept_opposite_is_whole
    {X : Type*} (horizon : Set X) :
    horizon \ (∅ : Set X) = horizon := by
  exact Set.sdiff_empty

/-- Boundary case: treating the whole horizon as the concept leaves no
relative remainder. -/
theorem whole_horizon_leaves_no_remainder
    {X : Type*} (horizon : Set X) :
    horizon \ horizon = ∅ := by
  exact Set.sdiff_self

#print axioms concept_boundary_iff_nonempty_remainder
#print axioms relative_opposite_is_proper_iff_concept_present
#print axioms relative_opposite_and_concept_cover_horizon
#print axioms equal_relative_opposites_iff_equal_concepts
#print axioms admissible_expressions_are_proper_parts
#print axioms dao_name_is_a_proper_part_under_the_same_premises
#print axioms empty_concept_opposite_is_whole
#print axioms whole_horizon_leaves_no_remainder

end D5.S3.ConceptDynamics.Negation.DaoConceptBoundarySpecialization
