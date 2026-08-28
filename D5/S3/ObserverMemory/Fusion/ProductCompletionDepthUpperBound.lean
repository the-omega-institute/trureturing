/- GID: D5/S3/ObserverMemory/Fusion/ProductCompletionDepthUpperBound
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/ProductCompletionDepthUpperBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The maximum local completion depth completes a pointwise product observer. -/

import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-26):
   * Exact family hits `futureReadoutWord` and `completeItinerary` supply the
     source's finite and complete behavior primitives and are used directly.
   * `SharpProductCompletionDepth.sharp_product_completion_depth` is not an
     exact hit: it assumes sharp witnesses and concludes equality of a least
     depth, while this theorem is only the source's upper-bound implication.
   * Pinned Mathlib hit `Finset.le_sup` supplies each local-to-maximum bound;
     no exact theorem for dependent pointwise observer products was found. -/

namespace D5.S3.ObserverMemory.Fusion.ProductCompletionDepthUpperBound

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If every factor's word through `localDepth i` determines its complete
itinerary, then the pointwise product word through the maximum local depth
determines the complete pointwise product itinerary. -/
theorem product_completion_depth_upper_bound
    {index : Type*} [Fintype index]
    {state output : index -> Type*}
    (update : forall i, state i -> state i)
    (readout : forall i, state i -> output i)
    (localDepth : index -> Nat)
    (localCompletion : forall i first second,
      futureReadoutWord (update i) (readout i) (localDepth i) first =
          futureReadoutWord (update i) (readout i) (localDepth i) second ->
        completeItinerary (update i) (readout i) first =
          completeItinerary (update i) (readout i) second) :
    forall first second : forall i, state i,
      futureReadoutWord
          (fun current i => update i (current i))
          (fun current i => readout i (current i))
          (Finset.univ.sup localDepth) first =
        futureReadoutWord
          (fun current i => update i (current i))
          (fun current i => readout i (current i))
          (Finset.univ.sup localDepth) second ->
      completeItinerary
          (fun current i => update i (current i))
          (fun current i => readout i (current i)) first =
        completeItinerary
          (fun current i => update i (current i))
          (fun current i => readout i (current i)) second := by
  classical
  intro first second sameWord
  have pointwiseIterate : forall depth (current : forall i, state i) i,
      ((fun configuration i => update i (configuration i))^[depth]) current i =
        ((update i)^[depth]) (current i) := by
    intro depth
    induction depth with
    | zero =>
        intro current i
        rfl
    | succ depth ih =>
        intro current i
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
  funext depth
  funext i
  have localWordEquality :
      futureReadoutWord (update i) (readout i) (localDepth i) (first i) =
        futureReadoutWord (update i) (readout i) (localDepth i) (second i) := by
    funext k
    have localLeMaximum : localDepth i <= Finset.univ.sup localDepth :=
      Finset.le_sup (s := Finset.univ) (f := localDepth) (Finset.mem_univ i)
    let globalK : Fin (Finset.univ.sup localDepth + 1) :=
      ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_succ localLeMaximum)⟩
    have globalCoordinate := congrFun (congrFun sameWord globalK) i
    simpa only [futureReadoutWord, pointwiseIterate] using globalCoordinate
  have localItineraryEquality :=
    localCompletion i (first i) (second i) localWordEquality
  simpa only [completeItinerary, pointwiseIterate] using
    congrFun localItineraryEquality depth

#print axioms product_completion_depth_upper_bound

end D5.S3.ObserverMemory.Fusion.ProductCompletionDepthUpperBound
