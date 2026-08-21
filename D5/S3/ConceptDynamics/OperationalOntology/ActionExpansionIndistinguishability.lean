/- GID: D5/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/OperationalOntology/ActionExpansionIndistinguishability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Show that enlarging the allowed action set shrinks behavioral indistinguishability. -/

/- Library-search audit trail (2026-08-22):
   * The source defines behavioral equivalence by equal public output after every
     action in the allowed set.
   * Repository searches found no accepted theorem for nested sets of
     already-composed actions; word-based controlled behavior is a different carrier.
   * Exact pinned-Mathlib hit `Set.biInter_subset_biInter_left` in
     `Mathlib.Data.Set.Lattice` is applied directly below.
-/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Set.Lattice

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.OperationalOntology.ActionExpansionIndistinguishability

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- State pairs with equal public output after every action in an allowed set. -/
def actionIndistinguishability {Action State Output : Type _}
    (allowed : Set Action) (act : Action → State → State)
    (observe : Concept State Output) : Set (State × State) :=
  ⋂ action ∈ allowed,
    {pair | observe (act action pair.1) = observe (act action pair.2)}

/-- Expanding the allowed action set can only shrink behavioral indistinguishability. -/
theorem action_expansion_shrinks_indistinguishability
    {Action State Output : Type _}
    (original expanded : Set Action) (act : Action → State → State)
    (observe : Concept State Output) (hExpansion : original ⊆ expanded) :
    actionIndistinguishability expanded act observe ⊆
      actionIndistinguishability original act observe := by
  unfold actionIndistinguishability
  exact Set.biInter_subset_biInter_left hExpansion

/-- The inclusion can be strict: adding the identity action distinguishes the
two Boolean states that an empty action set cannot distinguish. -/
example :
    (false, true) ∈ actionIndistinguishability (∅ : Set Unit)
        (fun _ => id) (id : Concept Bool Bool) ∧
      (false, true) ∉ actionIndistinguishability ({()} : Set Unit)
        (fun _ => id) (id : Concept Bool Bool) := by
  simp [actionIndistinguishability]

#print axioms action_expansion_shrinks_indistinguishability

end D5.S3.ConceptDynamics.OperationalOntology.ActionExpansionIndistinguishability
