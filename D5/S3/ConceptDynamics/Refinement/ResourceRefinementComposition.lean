/- GID: D5/S3/ConceptDynamics/Refinement/ResourceRefinementComposition
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Refinement/ResourceRefinementComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Resource-bounded factorization witnesses compose under a monotone cost model. -/

import D5.S3.ConceptDynamics.ConceptJoinUniversal

/- Library-search audit trail (2026-08-21):
   * `rg -n 'def Refines|Concept X' D5/S3/ConceptDynamics` found the canonical
     factorization relation and concept carrier in `ConceptJoinUniversal` and
     `ConceptFiberDecomposition`; both are imported directly.
   * No accepted declaration contains a resource-bounded refinement predicate or
     its composition law. `D5/S0/Naming/TranslationComposition` has a different
     partial-name/resource-modulus structure, so it is not a statement match.
   * Pinned-library searches for a generic bounded-factorization composition
     theorem found no exact hit; the proof below composes the source factor maps
     and applies the supplied cost-model law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Refinement.ResourceRefinementComposition

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal

universe u

/- A cost model assigns a natural resource cost to every map between carriers in
the same universe. -/
abbrev ResourceCost := {A B : Type u} → (A → B) → Nat

/- Resource refinement is the source factorization condition together with a
public budget bound on the witnessing recovery map. -/
def ResourceRefines {X C D : Type u}
    (cost : ResourceCost) (budget : Nat)
    (q_C : Concept X C) (q_D : Concept X D) : Prop :=
  ∃ factor : D → C,
    q_C = factor ∘ q_D ∧ cost factor ≤ budget

/- The two source budgets compose through the declared resource operation. -/
theorem resource_refinement_compose
    {X C D E : Type u}
    (cost : ResourceCost)
    (combine : Nat → Nat → Nat)
    (composition_bound :
      ∀ {A B C : Type u} (p : B → C) (q : A → B),
        cost (p ∘ q) ≤ combine (cost p) (cost q))
    (combine_mono :
      ∀ {r r' s s' : Nat}, r ≤ r' → s ≤ s' → combine r s ≤ combine r' s')
    (q_C : Concept X C) (q_D : Concept X D) (q_E : Concept X E)
    (r s : Nat)
    (h_CD : ResourceRefines cost r q_C q_D)
    (h_DE : ResourceRefines cost s q_D q_E) :
    ResourceRefines cost (combine r s) q_C q_E ∧
      (combine r s = r + s → ResourceRefines cost (r + s) q_C q_E) := by
  rcases h_CD with ⟨p, hp, hp_cost⟩
  rcases h_DE with ⟨q, hq, hq_cost⟩
  have h_composed_cost : cost (p ∘ q) ≤ combine r s := by
    calc
      cost (p ∘ q) ≤ combine (cost p) (cost q) := composition_bound p q
      _ ≤ combine r s := combine_mono hp_cost hq_cost
  have h_composed : ResourceRefines cost (combine r s) q_C q_E := by
    refine ⟨p ∘ q, ?_, h_composed_cost⟩
    rw [hp, hq]
    unfold Function.comp
    rfl
  refine ⟨h_composed, ?_⟩
  intro hadd
  simpa [hadd] using h_composed

example {X C D E : Type u}
    (cost : ResourceCost)
    (combine : Nat → Nat → Nat)
    (composition_bound :
      ∀ {A B C : Type u} (p : B → C) (q : A → B),
        cost (p ∘ q) ≤ combine (cost p) (cost q))
    (combine_mono :
      ∀ {r r' s s' : Nat}, r ≤ r' → s ≤ s' → combine r s ≤ combine r' s')
    (q_C : Concept X C) (q_D : Concept X D) (q_E : Concept X E)
    (r s : Nat)
    (h_CD : ResourceRefines cost r q_C q_D)
    (h_DE : ResourceRefines cost s q_D q_E) :
    ResourceRefines cost (combine r s) q_C q_E :=
  (resource_refinement_compose cost combine composition_bound combine_mono
    q_C q_D q_E r s h_CD h_DE).1

example :
    let cost : ResourceCost := fun {_ _} _ => 0
    ResourceRefines cost 0 (id : Concept Bool Bool) (id : Concept Bool Bool) := by
  dsimp [ResourceRefines]
  exact ⟨id, rfl, by simp⟩

example :
    let cost : ResourceCost := fun {_ _} _ => 0
    let combine : Nat → Nat → Nat := max
    (∀ {A B C : Type u} (p : B → C) (q : A → B),
      cost (p ∘ q) ≤ combine (cost p) (cost q)) ∧
      (∀ {r r' s s' : Nat}, r ≤ r' → s ≤ s' →
        combine r s ≤ combine r' s') := by
  dsimp
  constructor
  · intro A B C p q
    simp
  · intro r r' s s' hr hs
    omega

#print axioms resource_refinement_compose

end D5.S3.ConceptDynamics.Refinement.ResourceRefinementComposition
