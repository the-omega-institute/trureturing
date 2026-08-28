/- GID: D5/S3/ObserverMemory/Fusion/FamilyIndexedProductCompletion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/FamilyIndexedProductCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite independent readouts have a product completion and pointwise dynamics. -/

import D5.S3.ObserverMemory.Refinement.PredictionCompletion

/- Library-search audit trail (2026-08-26):
   * Exact repository hits `CompletedState`, `completionProjection`,
     `completionUpdate`, and `completeItinerary` supply the canonical
     predictive-completion primitives and are imported and applied directly.
   * The frozen `IndependentProductCompletion` theorem covers only two factors;
     repository name and body-shape searches found no family-indexed theorem.
   * Pinned Mathlib's exact `Setoid.piQuotientEquiv`, composed with
     `Quotient.congrRight`, supplies the indexed quotient equivalence. The
     composition follows the pinned `Subgroup.index_pi` proof shape.
   * `loogle` and `leansearch` were unavailable on PATH. -/

namespace D5.S3.ObserverMemory.Fusion.FamilyIndexedProductCompletion

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem pointwise_update_iterate
    {I : Type*} {Y : I -> Type*}
    (tau : forall i, Y i -> Y i)
    (configuration : forall i, Y i) (depth : Nat) (i : I) :
    ((fun current i => tau i (current i))^[depth]) configuration i =
      ((tau i)^[depth]) (configuration i) := by
  induction depth generalizing configuration with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]

private theorem pointwise_complete_itinerary
    {I : Type*} {Y O : I -> Type*}
    (tau : forall i, Y i -> Y i)
    (q : forall i, Y i -> O i)
    (configuration : forall i, Y i) (depth : Nat) (i : I) :
    completeItinerary
        (fun current i => tau i (current i))
        (fun current i => q i (current i)) configuration depth i =
      completeItinerary (tau i) (q i) (configuration i) depth := by
  simp only [completeItinerary, pointwise_update_iterate]

private theorem product_completion_relation
    {I : Type*} {Y O : I -> Type*}
    (tau : forall i, Y i -> Y i)
    (q : forall i, Y i -> O i)
    (first second : forall i, Y i) :
    Setoid.ker
        (completeItinerary
          (fun current i => tau i (current i))
          (fun current i => q i (current i))) first second <->
      @piSetoid I Y
        (fun i => Setoid.ker (completeItinerary (tau i) (q i))) first second := by
  constructor
  · intro h i
    funext depth
    have coordinateEquality := congrFun (congrFun h depth) i
    simpa only [pointwise_complete_itinerary] using coordinateEquality
  · intro h
    funext depth i
    have coordinateEquality := congrFun (h i) depth
    simpa only [pointwise_complete_itinerary] using coordinateEquality

/-- The canonical equivalence sends a global predictive class to its family of
coordinate predictive classes. -/
noncomputable def familyProductCompletionEquiv
    {I : Type*} [Fintype I] {Y O : I -> Type*}
    (tau : forall i, Y i -> Y i)
    (q : forall i, Y i -> O i) :
    CompletedState
        (fun current i => tau i (current i))
        (fun current i => q i (current i)) ≃
      forall i, CompletedState (tau i) (q i) :=
  (Quotient.congrRight (product_completion_relation tau q)).trans
    (Setoid.piQuotientEquiv
      (fun i => Setoid.ker (completeItinerary (tau i) (q i)))).symm

private theorem family_product_completion_equiv_projection
    {I : Type*} [Fintype I] {Y O : I -> Type*}
    (tau : forall i, Y i -> Y i)
    (q : forall i, Y i -> O i)
    (configuration : forall i, Y i) :
    familyProductCompletionEquiv tau q
        (completionProjection
          (fun current i => tau i (current i))
          (fun current i => q i (current i)) configuration) =
      fun i => completionProjection (tau i) (q i) (configuration i) := by
  change
    ((Quotient.congrRight (product_completion_relation tau q)).trans
      (Setoid.piQuotientEquiv
        (fun i => Setoid.ker (completeItinerary (tau i) (q i)))).symm)
        (Quotient.mk _ configuration) = _
  rw [Equiv.trans_apply]
  have congruentRepresentative :
      Quotient.congrRight (product_completion_relation tau q)
          (Quotient.mk _ configuration) =
        Quotient.mk _ configuration := rfl
  rw [congruentRepresentative]
  rfl

/-- The canonical family equivalence acts coordinatewise on projections and
intertwines the product update with every component completion update. -/
theorem family_indexed_product_completion
    {I : Type*} [Fintype I] {Y O : I -> Type*}
    (tau : forall i, Y i -> Y i)
    (q : forall i, Y i -> O i) :
    let equivalence :
        CompletedState
            (fun current i => tau i (current i))
            (fun current i => q i (current i)) ≃
          forall i, CompletedState (tau i) (q i) :=
      familyProductCompletionEquiv tau q
    (forall configuration : forall i, Y i,
      equivalence
          (completionProjection
            (fun current i => tau i (current i))
            (fun current i => q i (current i)) configuration) =
        fun i => completionProjection (tau i) (q i) (configuration i)) /\
      (forall state : CompletedState
          (fun current i => tau i (current i))
          (fun current i => q i (current i)),
        equivalence
            (completionUpdate
              (fun current i => tau i (current i))
              (fun current i => q i (current i)) state) =
          fun i => completionUpdate (tau i) (q i) (equivalence state i)) := by
  dsimp only
  constructor
  · exact family_product_completion_equiv_projection tau q
  · intro state
    refine Quotient.inductionOn' state (fun configuration => ?_)
    change familyProductCompletionEquiv tau q
        (completionProjection
          (fun current i => tau i (current i))
          (fun current i => q i (current i))
          (fun i => tau i (configuration i))) =
      fun i => completionProjection (tau i) (q i) (tau i (configuration i))
    exact family_product_completion_equiv_projection tau q
      (fun i => tau i (configuration i))

#print axioms family_indexed_product_completion

end D5.S3.ObserverMemory.Fusion.FamilyIndexedProductCompletion
