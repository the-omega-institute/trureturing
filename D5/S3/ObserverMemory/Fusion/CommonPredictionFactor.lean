/- GID: D5/S3/ObserverMemory/Fusion/CommonPredictionFactor
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/CommonPredictionFactor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The dynamics-stable common prediction quotient has a unique surjective factor. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-21):
   * The repository's exact source-semantics primitive `completeItinerary` supplies
     both prediction relations; no equal or stronger dynamics-stable common-factor
     theorem was found in the existing fusion or prediction-factor families.
   * Exact pinned-Mathlib hits `Setoid.completeLattice`, `sInf_le`, and
     `Quotient.lift_surjective` respectively construct the least stable upper
     relation and prove the induced factor surjective; all are applied below.
   * Exact pinned-Mathlib hit `Setoid.lift_unique` supplies quotient-factor
     uniqueness and is applied below. Loogle found only these quotient components,
     while LeanSearch's query endpoint returned HTTP 404 and no usable theorem. -/

namespace D5.S3.ObserverMemory.Fusion.CommonPredictionFactor

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The least equivalence relation that contains both complete-future kernels and
is preserved by the source update. -/
def commonPredictionRelation {Y O1 O2 : Type*}
    (update : Y -> Y) (firstReadout : Y -> O1) (secondReadout : Y -> O2) :
    Setoid Y :=
  sInf { relation : Setoid Y |
    Setoid.ker (completeItinerary update firstReadout) <= relation /\
      Setoid.ker (completeItinerary update secondReadout) <= relation /\
      forall {left right}, relation left right ->
        relation (update left) (update right) }

/-- States modulo the dynamics-stable common prediction relation. -/
abbrev CommonPredictionCompletion {Y O1 O2 : Type*}
    (update : Y -> Y) (firstReadout : Y -> O1) (secondReadout : Y -> O2) :=
  Quotient (commonPredictionRelation update firstReadout secondReadout)

/-- The canonical projection to the common prediction completion. -/
def commonProjection {Y O1 O2 : Type*}
    (update : Y -> Y) (firstReadout : Y -> O1) (secondReadout : Y -> O2) :
    Y -> CommonPredictionCompletion update firstReadout secondReadout :=
  @Quotient.mk'' Y (commonPredictionRelation update firstReadout secondReadout)

/-- Any surjective dynamic factor computable from both prediction completions
factors uniquely and surjectively through their dynamics-stable common quotient. -/
theorem common_prediction_factor_universal_property
    {Y O1 O2 W : Type*}
    (update : Y -> Y) (firstReadout : Y -> O1) (secondReadout : Y -> O2)
    (factor : Y -> W) (factorUpdate : W -> W)
    (factorSurjective : Function.Surjective factor)
    (dynamicsFactor : Function.Semiconj factor update factorUpdate)
    (fromFirst : Quotient (Setoid.ker
      (completeItinerary update firstReadout)) -> W)
    (fromSecond : Quotient (Setoid.ker
      (completeItinerary update secondReadout)) -> W)
    (firstFactors : factor = fromFirst ∘
      @Quotient.mk'' Y (Setoid.ker
        (completeItinerary update firstReadout)))
    (secondFactors : factor = fromSecond ∘
      @Quotient.mk'' Y (Setoid.ker
        (completeItinerary update secondReadout))) :
    ExistsUnique fun descend :
        CommonPredictionCompletion update firstReadout secondReadout -> W =>
      Function.Surjective descend /\
        factor = descend ∘
          commonProjection update firstReadout secondReadout := by
  have firstBelow :
      Setoid.ker (completeItinerary update firstReadout) <= Setoid.ker factor := by
    intro left right relation
    calc
      factor left = fromFirst (Quotient.mk'' left) := congrFun firstFactors left
      _ = fromFirst (Quotient.mk'' right) :=
        congrArg fromFirst (Quotient.sound' relation)
      _ = factor right := (congrFun firstFactors right).symm
  have secondBelow :
      Setoid.ker (completeItinerary update secondReadout) <= Setoid.ker factor := by
    intro left right relation
    calc
      factor left = fromSecond (Quotient.mk'' left) := congrFun secondFactors left
      _ = fromSecond (Quotient.mk'' right) :=
        congrArg fromSecond (Quotient.sound' relation)
      _ = factor right := (congrFun secondFactors right).symm
  have kernelStable : forall {left right}, Setoid.ker factor left right ->
      Setoid.ker factor (update left) (update right) := by
    intro left right relation
    calc
      factor (update left) = factorUpdate (factor left) := dynamicsFactor left
      _ = factorUpdate (factor right) := congrArg factorUpdate relation
      _ = factor (update right) := (dynamicsFactor right).symm
  have commonBelow :
      commonPredictionRelation update firstReadout secondReadout <=
        Setoid.ker factor := by
    apply sInf_le
    exact ⟨firstBelow, secondBelow, kernelStable⟩
  let descend :
      CommonPredictionCompletion update firstReadout secondReadout -> W :=
    Quotient.lift factor commonBelow
  have descendSurjective : Function.Surjective descend := by
    exact Quotient.lift_surjective factor commonBelow factorSurjective
  have projectionFactors :
      factor = descend ∘ commonProjection update firstReadout secondReadout := by
    rfl
  refine ⟨descend, ⟨descendSurjective, projectionFactors⟩, ?_⟩
  intro candidate candidateProperty
  have liftUnique : Quotient.lift factor commonBelow = candidate := by
    apply Setoid.lift_unique
    simpa [commonProjection] using candidateProperty.2
  simpa [descend] using liftUnique.symm

#print axioms common_prediction_factor_universal_property

end D5.S3.ObserverMemory.Fusion.CommonPredictionFactor
