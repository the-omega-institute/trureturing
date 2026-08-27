/- GID: D5/S3/ConceptDynamics/Attribution/StabilizerSelectorObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/StabilizerSelectorObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fixed-point-free stabilizer obstructs every equivariant deterministic selector. -/

import Mathlib.GroupTheory.GroupAction.Defs

/- Library-search audit trail (2026-08-27):
   * The frozen `SymmetricEventNoUniqueCulprit` theorem is a finite-permutation
     specialization and does not cover general group actions or admissible sets.
   * Repository body-shape searches found no theorem combining a state
     stabilizer, its lack of admissible fixed actions, and selector equivariance.
   * Pinned Mathlib supplies `Group`, `MulAction`, and action notation, but no
     packaged equivariant-selector obstruction. -/

namespace D5.S3.ConceptDynamics.Attribution.StabilizerSelectorObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If every admissible action at a state is moved by some symmetry fixing
that state, no deterministic selector can be both admissible and equivariant. -/
theorem no_equivariant_selector_of_stabilizer_without_fixed_action
    {G X A : Type*} [Group G] [MulAction G X] [MulAction G A]
    (admissible : X -> Set A) (x : X)
    (hnoFixed : ∀ a ∈ admissible x,
      ∃ g : G, g • x = x ∧ g • a ≠ a) :
    ¬ ∃ selector : X -> A,
      (∀ y, selector y ∈ admissible y) ∧
        ∀ (g : G) (y : X), selector (g • y) = g • selector y := by
  rintro ⟨selector, hselects, hequivariant⟩
  rcases hnoFixed (selector x) (hselects x) with
    ⟨g, hfixesState, hmovesAction⟩
  apply hmovesAction
  calc
    g • selector x = selector (g • x) := (hequivariant g x).symm
    _ = selector x := congrArg selector hfixesState

#print axioms no_equivariant_selector_of_stabilizer_without_fixed_action

end D5.S3.ConceptDynamics.Attribution.StabilizerSelectorObstruction
