/- GID: D5/S3/ConceptDynamics/Adjunction/BestSafeAbstraction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Adjunction/BestSafeAbstraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The Galois-derived transformer is the most precise safe abstraction. -/

import Mathlib.Data.Set.Image
import Mathlib.Order.GaloisConnection.Defs

/- Library-search audit trail (2026-08-27):
   * Repository searches for safe abstractions, concretization, and best Galois-derived
     transformers found only the adjacent concept-process adjunction, not this theorem.
   * Body-shape searches for `abstraction` composed with a direct-image transformer and
     `concretization` found no D5 primitive, so the source construction is exposed as a public
     `let` rather than introduced as a sibling definition.
   * Pinned Mathlib provides `GaloisConnection.le_u_l` for safety and the defining adjunction
     equivalence for pointwise precision. No theorem packages both public clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Adjunction.BestSafeAbstraction

/-- The canonical abstract transformer obtained by abstracting the direct image of each
concretized state is safe, and every other safe transformer is pointwise above it. -/
theorem best_safe_abstraction
    {X Abstract : Type*} [Preorder Abstract]
    (abstraction : Set X -> Abstract) (concretization : Abstract -> Set X)
    (connection : GaloisConnection abstraction concretization)
    (process : X -> X) :
    let best : Abstract -> Abstract :=
      abstraction ∘ (fun states => process '' states) ∘ concretization
    (∀ abstractState,
      process '' concretization abstractState ⊆
        concretization (best abstractState)) ∧
    (∀ candidate : Abstract -> Abstract,
      (∀ abstractState,
        process '' concretization abstractState ⊆
          concretization (candidate abstractState)) ->
      ∀ abstractState, best abstractState ≤ candidate abstractState) := by
  dsimp only [Function.comp_apply]
  constructor
  · intro abstractState
    exact connection.le_u_l (process '' concretization abstractState)
  · intro candidate candidateSafe abstractState
    exact (connection _ _).mpr (candidateSafe abstractState)

#print axioms best_safe_abstraction

end D5.S3.ConceptDynamics.Adjunction.BestSafeAbstraction
