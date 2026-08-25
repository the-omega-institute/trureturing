/- GID: D5/S3/ConceptDynamics/Aggregation/IndividualRationalityMajorityCycle
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Aggregation/IndividualRationalityMajorityCycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transitive complete individual rankings produce a nontransitive majority cycle. -/

import D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
import Mathlib.Data.Real.Basic

/- Library-search audit trail (2026-08-25):
   * Exact D5 hits `prefers`, `majorityPrefers`, and
     `majority_cycle_not_scalar_order` construct the source's cyclic profile and
     prove its scalar-order obstruction. They are imported and applied directly.
   * The frozen theorem does not publicly state individual transitivity,
     completeness, the three cycle edges, or majority nontransitivity together,
     so it is not an exact receipt-only bind for this atom.
   * Pinned Mathlib searches for Condorcet cycles and majority transitivity found
     no full-statement theorem. `loogle` and `leansearch` are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Aggregation.IndividualRationalityMajorityCycle

open D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder

/-- The three displayed individual rankings are transitive and complete, while
their pairwise majority relation contains the full directed cycle, is not
transitive, and has no faithful real-valued ordering. -/
theorem individual_rationality_majority_cycle :
    (forall voter x y z : Fin 3,
      prefers voter x y -> prefers voter y z -> prefers voter x z) ∧
    (forall voter x y : Fin 3,
      x ≠ y -> prefers voter x y ∨ prefers voter y x) ∧
    majorityPrefers 0 1 ∧
    majorityPrefers 1 2 ∧
    majorityPrefers 2 0 ∧
    ¬(forall ⦃x y z : Fin 3⦄,
      majorityPrefers x y -> majorityPrefers y z -> majorityPrefers x z) ∧
    ¬∃ utility : Fin 3 -> Real,
      forall x y, majorityPrefers x y -> utility x > utility y := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro majorityTransitive
    have zeroBeatsOne : majorityPrefers (0 : Fin 3) 1 := by decide
    have oneBeatsTwo : majorityPrefers (1 : Fin 3) 2 := by decide
    have zeroBeatsTwo : majorityPrefers 0 2 :=
      majorityTransitive zeroBeatsOne oneBeatsTwo
    exact (by decide : ¬majorityPrefers 0 2) zeroBeatsTwo
  · exact majority_cycle_not_scalar_order (Utility := Real)

#print axioms individual_rationality_majority_cycle

end D5.S3.ConceptDynamics.Aggregation.IndividualRationalityMajorityCycle
