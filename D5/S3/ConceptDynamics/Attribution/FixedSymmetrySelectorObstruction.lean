/- GID: D5/S3/ConceptDynamics/Attribution/FixedSymmetrySelectorObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/FixedSymmetrySelectorObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-state symmetry obstructs equivariant admissible selection. -/

import D5.S3.ConceptDynamics.Attribution.StabilizerSelectorObstruction

/- Library-search audit trail (2026-08-27):
   * The imported family owner proves the stronger obstruction where the
     stabilizer element may depend on the selected admissible action.
   * Repository searches found only that owner and a finite-permutation
     specialization, not the source's one-common-symmetry statement.
   * Pinned Mathlib supplies the group-action primitives but no packaged
     equivariant-selector obstruction with an admissible-set clause. -/

namespace D5.S3.ConceptDynamics.Attribution.FixedSymmetrySelectorObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.Attribution.StabilizerSelectorObstruction

/-- If one group element fixes a state while moving every admissible action
there, no everywhere-admissible deterministic selector can be equivariant. -/
theorem no_equivariant_selector_of_common_fixed_symmetry
    {G X A : Type*} [Group G] [MulAction G X] [MulAction G A]
    (admissible : X -> Set A) :
    (∃ x : X, ∃ g : G,
      g • x = x ∧ ∀ a ∈ admissible x, g • a ≠ a) ->
      ¬ ∃ selector : X -> A,
        (∀ y, selector y ∈ admissible y) ∧
          ∀ (g : G) (y : X), selector (g • y) = g • selector y := by
  rintro ⟨x, g, hfixesState, hmovesActions⟩
  exact no_equivariant_selector_of_stabilizer_without_fixed_action
    admissible x (fun a ha => ⟨g, hfixesState, hmovesActions a ha⟩)

#print axioms no_equivariant_selector_of_common_fixed_symmetry

end D5.S3.ConceptDynamics.Attribution.FixedSymmetrySelectorObstruction
