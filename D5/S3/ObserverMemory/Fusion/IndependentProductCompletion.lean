/- GID: D5/S3/ObserverMemory/Fusion/IndependentProductCompletion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/IndependentProductCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Independent product readouts have a product predictive completion and componentwise quotient dynamics. -/

import D5.S3.ObserverMemory.Refinement.PredictionCompletion

/- Library-search audit trail (2026-08-21):
   * Exact local hits `CompletedState`, `completionProjection`, `completionUpdate`,
     and `completeItinerary` from `PredictionCompletion` are imported and used
     directly for the source's predictive quotients and their dynamics.
   * `CompatibleFusionEmbedding.compatible_fusion_embedding` is an adjacent
     general compatible-image theorem, but it does not state the independent
     product equivalence; the present theorem supplies that missing hypothesis.
   * Pinned Mathlib's `Quotient.lift`, `Quotient.sound'`, `Quotient.exact`, and
     `Equiv.ofBijective` are the direct quotient and bijection primitives used.
   * No exact theorem for independent product predictive completions was found;
     `loogle` and `leansearch` were unavailable on PATH.
-/

namespace D5.S3.ObserverMemory.Fusion.IndependentProductCompletion

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

def productUpdate {Y₁ Y₂ : Type*} (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂) :
    Y₁ × Y₂ → Y₁ × Y₂ :=
  fun state => (tau₁ state.1, tau₂ state.2)

def productReadout {Y₁ Y₂ O₁ O₂ : Type*}
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂) :
    Y₁ × Y₂ → O₁ × O₂ :=
  fun state => (q₁ state.1, q₂ state.2)

private theorem product_update_iterate
    {Y₁ Y₂ : Type*} (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (state : Y₁ × Y₂) (n : Nat) :
    (productUpdate tau₁ tau₂)^[n] state =
      ((tau₁^[n]) state.1, (tau₂^[n]) state.2) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih]
      rfl

private theorem product_complete_itinerary
    {Y₁ Y₂ O₁ O₂ : Type*}
    (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂)
    (state : Y₁ × Y₂) (n : Nat) :
    completeItinerary (productUpdate tau₁ tau₂) (productReadout q₁ q₂)
        state n =
      (completeItinerary tau₁ q₁ state.1 n,
        completeItinerary tau₂ q₂ state.2 n) := by
  change productReadout q₁ q₂
      ((productUpdate tau₁ tau₂)^[n] state) =
    (q₁ ((tau₁^[n]) state.1), q₂ ((tau₂^[n]) state.2))
  rw [product_update_iterate]
  rfl

noncomputable def productCompletionMap
    {Y₁ Y₂ O₁ O₂ : Type*}
    (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂) :
    CompletedState (productUpdate tau₁ tau₂) (productReadout q₁ q₂) →
      CompletedState tau₁ q₁ × CompletedState tau₂ q₂ :=
  Quotient.lift
    (fun state =>
      (completionProjection tau₁ q₁ state.1,
        completionProjection tau₂ q₂ state.2))
    (by
      intro state state' hstate
      apply Prod.ext
      · apply Quotient.sound'
        funext n
        simpa only [product_complete_itinerary] using
          congrArg Prod.fst (congrFun hstate n)
      · apply Quotient.sound'
        funext n
        simpa only [product_complete_itinerary] using
          congrArg Prod.snd (congrFun hstate n))

private theorem product_completion_map_injective
    {Y₁ Y₂ O₁ O₂ : Type*}
    (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂) :
    Function.Injective (productCompletionMap tau₁ tau₂ q₁ q₂) := by
  intro first second hfirst
  obtain ⟨state, rfl⟩ := Quotient.exists_rep first
  obtain ⟨state', rfl⟩ := Quotient.exists_rep second
  apply Quotient.sound'
  funext n
  apply Prod.ext
  · rw [product_complete_itinerary tau₁ tau₂ q₁ q₂ state n,
      product_complete_itinerary tau₁ tau₂ q₁ q₂ state' n]
    exact congrFun (Quotient.exact (congrArg Prod.fst hfirst)) n
  · rw [product_complete_itinerary tau₁ tau₂ q₁ q₂ state n,
      product_complete_itinerary tau₁ tau₂ q₁ q₂ state' n]
    exact congrFun (Quotient.exact (congrArg Prod.snd hfirst)) n

private theorem product_completion_map_surjective
    {Y₁ Y₂ O₁ O₂ : Type*}
    (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂) :
    Function.Surjective (productCompletionMap tau₁ tau₂ q₁ q₂) := by
  intro target
  obtain ⟨state₁, h₁⟩ := Quotient.exists_rep target.1
  obtain ⟨state₂, h₂⟩ := Quotient.exists_rep target.2
  refine ⟨Quotient.mk'' (state₁, state₂), ?_⟩
  apply Prod.ext
  · exact h₁
  · exact h₂

noncomputable def productCompletionEquiv
    {Y₁ Y₂ O₁ O₂ : Type*}
    (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂) :
    CompletedState (productUpdate tau₁ tau₂) (productReadout q₁ q₂) ≃
      CompletedState tau₁ q₁ × CompletedState tau₂ q₂ :=
  Equiv.ofBijective (productCompletionMap tau₁ tau₂ q₁ q₂)
    ⟨product_completion_map_injective tau₁ tau₂ q₁ q₂,
      product_completion_map_surjective tau₁ tau₂ q₁ q₂⟩

theorem product_completion_dynamics
    {Y₁ Y₂ O₁ O₂ : Type*}
    (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂)
    (state : CompletedState (productUpdate tau₁ tau₂)
      (productReadout q₁ q₂)) :
    productCompletionMap tau₁ tau₂ q₁ q₂
        (completionUpdate (productUpdate tau₁ tau₂)
          (productReadout q₁ q₂) state) =
      (completionUpdate tau₁ q₁
          (productCompletionMap tau₁ tau₂ q₁ q₂ state).1,
        completionUpdate tau₂ q₂
          (productCompletionMap tau₁ tau₂ q₁ q₂ state).2) := by
  refine Quotient.inductionOn' state (fun representative => ?_)
  rfl

/-- Independent component systems have a product predictive completion, and
the induced update is the product of the two component quotient updates. -/
theorem independent_product_completion
    {Y₁ Y₂ O₁ O₂ : Type*}
    (tau₁ : Y₁ → Y₁) (tau₂ : Y₂ → Y₂)
    (q₁ : Y₁ → O₁) (q₂ : Y₂ → O₂) :
    Nonempty (CompletedState (productUpdate tau₁ tau₂)
      (productReadout q₁ q₂) ≃
      CompletedState tau₁ q₁ × CompletedState tau₂ q₂) ∧
      (∀ state : CompletedState (productUpdate tau₁ tau₂)
          (productReadout q₁ q₂),
        productCompletionMap tau₁ tau₂ q₁ q₂
            (completionUpdate (productUpdate tau₁ tau₂)
              (productReadout q₁ q₂) state) =
          (completionUpdate tau₁ q₁
              (productCompletionMap tau₁ tau₂ q₁ q₂ state).1,
            completionUpdate tau₂ q₂
              (productCompletionMap tau₁ tau₂ q₁ q₂ state).2)) := by
  exact ⟨⟨productCompletionEquiv tau₁ tau₂ q₁ q₂⟩,
    product_completion_dynamics tau₁ tau₂ q₁ q₂⟩

example :
    Nonempty (CompletedState (productUpdate (id : Unit → Unit) (id : Unit → Unit))
      (productReadout (id : Unit → Unit) (id : Unit → Unit)) ≃
      CompletedState (id : Unit → Unit) (id : Unit → Unit) ×
        CompletedState (id : Unit → Unit) (id : Unit → Unit)) :=
  (independent_product_completion
    (id : Unit → Unit) (id : Unit → Unit)
    (id : Unit → Unit) (id : Unit → Unit)).1

#print axioms independent_product_completion

end D5.S3.ObserverMemory.Fusion.IndependentProductCompletion
