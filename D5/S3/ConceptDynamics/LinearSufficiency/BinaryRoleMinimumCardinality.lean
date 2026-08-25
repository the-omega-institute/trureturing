/- GID: D5/S3/ConceptDynamics/LinearSufficiency/BinaryRoleMinimumCardinality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/LinearSufficiency/BinaryRoleMinimumCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Minimum sufficient binary role cardinality equals the span dimension. -/

import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/- Library-search audit trail (2026-08-25):
   * Repository searches for minimum sufficient subfamilies, spanning-subfamily
     cardinality, and the corresponding body shapes found no exact D5 theorem.
   * `Submodule.spanFinrank_eq_iInf` is adjacent but minimizes over arbitrary
     generating finsets and does not retain the required subset-of-candidates clause.
   * Mathlib's `exists_linearIndependent` gives a linearly independent subset
     with the same span. `rank_span_set` and `rank_span_le` give cardinal
     attainment and the universal lower bound without a finiteness restriction.
   * No new definition or abbreviation is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.LinearSufficiency.BinaryRoleMinimumCardinality

/-- Among subfamilies selected from a binary role family and spanning the
same role space, the least cardinality is the dimension of that span. -/
theorem binary_role_minimum_cardinality
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (candidates : Set V) :
    IsLeast
      {cardinality : Cardinal | exists chosen : Set V,
        chosen ⊆ candidates /\
        Submodule.span (ZMod 2) chosen =
          Submodule.span (ZMod 2) candidates /\
        Cardinal.mk chosen = cardinality}
      (Module.rank (ZMod 2) (Submodule.span (ZMod 2) candidates)) := by
  obtain ⟨chosen, chosen_subset, same_span, chosen_independent⟩ :=
    exists_linearIndependent (ZMod 2) candidates
  constructor
  · refine ⟨chosen, chosen_subset, ?_, ?_⟩
    · exact same_span
    · rw [← same_span, rank_span_set chosen_independent]
  · intro cardinality
    rintro ⟨other, _other_subset, other_span, rfl⟩
    rw [← other_span]
    exact rank_span_le other

#print axioms binary_role_minimum_cardinality

end D5.S3.ConceptDynamics.LinearSufficiency.BinaryRoleMinimumCardinality
