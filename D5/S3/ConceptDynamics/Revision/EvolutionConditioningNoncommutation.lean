/- GID: D5/S3/ConceptDynamics/Revision/EvolutionConditioningNoncommutation
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Revision/EvolutionConditioningNoncommutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evolution and conditioning can fail to commute, but invariant evidence restores it. -/

import Mathlib.Data.Set.Image

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'evolution_and_conditioning_do_not_commute' D5
     Golden/Frozen/accepted` returned no matches.
   * Searches for `Commute|commut`, revision, conditioning, and image/intersection
     declarations found only topic-distinct D5 results, not this counterexample.
   * Pinned Mathlib provides `Set.image_inter_preimage`; it is reused directly to
     prove the positive result under invariance of the evidence predicate.
   * `Set.image_inter` also exists for injective maps, but the preimage lemma proves
     the desired result without the unnecessary injectivity assumption. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Revision.EvolutionConditioningNoncommutation

/-- Conditioning restricts the currently admitted states to the evidence set. -/
def conditioning {X : Type*} (P A : Set X) : Set X :=
  A ∩ P

/-- A pointwise state transition evolves a set by taking its direct image. -/
def imageEvolution {X : Type*} (f : X → X) (A : Set X) : Set X :=
  f '' A

/-- The counterexample evolution sends every nonempty set to the whole state space. -/
def saturatingEvolution {X : Type*} (A : Set X) : Set X :=
  fun _ => A.Nonempty

/-- Evolution and conditioning do not commute for all state spaces and evolutions:
there is a concrete counterexample. -/
theorem evolution_and_conditioning_do_not_commute :
    ∃ (X : Type) (F : Set X → Set X) (P A : Set X),
      F (A ∩ P) ≠ F A ∩ P := by
  refine ⟨Bool, saturatingEvolution, {true}, {false}, ?_⟩
  intro h
  have htrue := Set.ext_iff.mp h true
  change
    (({false} ∩ {true} : Set Bool).Nonempty ↔
      ({false} : Set Bool).Nonempty ∧ true ∈ ({true} : Set Bool)) at htrue
  simp at htrue

/-- An image evolution commutes with conditioning when the evidence predicate is
invariant under preimage. This conclusion needs no injectivity assumption. -/
theorem image_evolution_commutes_with_conditioning {X : Type*}
    (f : X → X) (P A : Set X) (hP : f ⁻¹' P = P) :
    imageEvolution f (conditioning P A) =
      conditioning P (imageEvolution f A) := by
  change f '' (A ∩ P) = f '' A ∩ P
  calc
    f '' (A ∩ P) = f '' (A ∩ f ⁻¹' P) := by rw [hP]
    _ = f '' A ∩ P := Set.image_inter_preimage f A P

/-- The Boolean counterexample is executable independently of the existential theorem. -/
example :
    let F : Set Bool → Set Bool := saturatingEvolution
    F ({false} ∩ {true}) ≠ F {false} ∩ {true} := by
  dsimp only
  intro h
  have htrue := Set.ext_iff.mp h true
  change
    (({false} ∩ {true} : Set Bool).Nonempty ↔
      ({false} : Set Bool).Nonempty ∧ true ∈ ({true} : Set Bool)) at htrue
  simp at htrue

#print axioms evolution_and_conditioning_do_not_commute

end D5.S3.ConceptDynamics.Revision.EvolutionConditioningNoncommutation
