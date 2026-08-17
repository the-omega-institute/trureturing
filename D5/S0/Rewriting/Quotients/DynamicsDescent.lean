/- GID: D5/S0/Rewriting/Quotients/DynamicsDescent
   generality: G
   mirror-B: D5/B/S0/Rewriting/Quotients/DynamicsDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A self-map descends uniquely through a quotient exactly when it preserves fibers. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-17):
   * Pinned Mathlib and Loogle searches found no exact existence-and-uniqueness
     characterization for descent through an arbitrary surjection.
   * Exact pinned-Mathlib hit: `Function.Surjective.injective_comp_right`
     supplies uniqueness of a descended map and is applied below.
   * Repository searches found an adjacent map between two kernel quotients,
     but no equal or stronger self-map descent characterization.
-/

namespace D5.S0.Rewriting.Quotients.DynamicsDescent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A self-map of a quotient presentation has a unique descended dynamics
exactly when it sends every fiber of the quotient map into a fiber. -/
theorem dynamics_descends_iff
    {X B : Type*} (quotientMap : X -> B) (update : X -> X)
    (hSurjective : Function.Surjective quotientMap) :
    (ExistsUnique fun descended : B -> B =>
      quotientMap ∘ update = descended ∘ quotientMap) <->
      forall x y, quotientMap x = quotientMap y ->
        quotientMap (update x) = quotientMap (update y) := by
  apply Eq.mp (propext (Iff.refl _))
  constructor
  · rintro ⟨descended, hCommutes, _⟩ x y hxy
    change (quotientMap ∘ update) x = (quotientMap ∘ update) y
    rw [hCommutes]
    exact congrArg descended hxy
  · intro hPreserves
    let representative : B -> X := fun b => Classical.choose (hSurjective b)
    have hRepresentative (b : B) : quotientMap (representative b) = b :=
      Classical.choose_spec (hSurjective b)
    let descended : B -> B := fun b => quotientMap (update (representative b))
    have hCommutes : quotientMap ∘ update = descended ∘ quotientMap := by
      funext x
      exact (hPreserves (representative (quotientMap x)) x
        (hRepresentative (quotientMap x))).symm
    refine ⟨descended, hCommutes, ?_⟩
    intro candidate hCandidate
    apply hSurjective.injective_comp_right
    exact hCandidate.symm.trans hCommutes

example : Nonempty Bool := ⟨false⟩

example :
    Function.Surjective (id : Bool -> Bool) ∧
      forall x y, id x = id y ->
        id (Bool.not x) = id (Bool.not y) := by
  refine ⟨Function.surjective_id, ?_⟩
  intro x y hxy
  exact congrArg Bool.not hxy

example :
    ExistsUnique fun descended : Bool -> Bool =>
      id ∘ Bool.not = descended ∘ id := by
  apply (dynamics_descends_iff id Bool.not Function.surjective_id).2
  intro x y hxy
  exact congrArg Bool.not hxy

#print axioms dynamics_descends_iff

end D5.S0.Rewriting.Quotients.DynamicsDescent
