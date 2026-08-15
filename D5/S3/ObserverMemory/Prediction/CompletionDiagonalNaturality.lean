/- GID: D5/S3/ObserverMemory/Prediction/CompletionDiagonalNaturality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/CompletionDiagonalNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Projection to the future quotient commutes with twisted diagonalization. -/

import D5.S0.Diagonal.Naturality.CoordinateRestrictionNaturality
import D5.S3.ObserverMemory.Prediction.ItineraryCompletion

/- Library-search audit trail (2026-08-16):
   * Repository search found the exact general support theorem
     `coordinate_restriction_naturality`; it is imported and applied below.
   * Repository search found the frozen complete-itinerary quotient and its
     transported update in `ItineraryCompletion`; both are reused below.
   * Loogle found the exact pinned-Mathlib computation `Quotient.map_mk`, but
     the frozen quotient update is transported through the kernel-range
     equivalence rather than defined by `Quotient.map`, so no new map is made.
   * LeanSearch's query endpoint returned HTTP 404 for the quotient-map search.
   * No repository, pinned-Mathlib, Loogle, or LeanSearch result stated the
     complete quotient diagonal identity itself.
-/

namespace D5.S3.ObserverMemory.Prediction.CompletionDiagonalNaturality

open D5.S0.Diagonal
open D5.S0.Diagonal.Naturality.CoordinateRestrictionNaturality
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion

universe u v w

/-- Pointwise projection to the complete future quotient commutes with twisted
diagonalization, whose quotient twist is the canonically transported update. -/
theorem completion_quotient_diagonal_naturality
    {A : Type u} {Y : Type v} {O : Type w}
    (tau : Y -> Y) (q : Y -> O) (E : A -> A -> Y) :
    (fun a =>
      (@Quotient.mk'' Y (Setoid.ker (completeItinerary tau q)))
        (EscapeCount.diagonal tau E a)) =
      EscapeCount.diagonal (quotientUpdate tau q)
        (fun a b =>
          (@Quotient.mk'' Y (Setoid.ker (completeItinerary tau q))) (E a b)) := by
  let projection : Y -> Quotient (Setoid.ker (completeItinerary tau q)) :=
    Quotient.mk''
  have hprojection :
      projection ∘ tau = quotientUpdate tau q ∘ projection := by
    funext y
    apply (Setoid.quotientKerEquivRange (completeItinerary tau q)).injective
    apply Subtype.ext
    funext n
    simp [projection, quotientUpdate, itineraryUpdate,
      Setoid.quotientKerEquivRange, Setoid.quotientKerEquivRangeKerLift,
      Setoid.kerLift, completeItinerary, Function.iterate_succ_apply]
  have h := coordinate_restriction_naturality
    (iota := Function.Embedding.refl A) projection tau (quotientUpdate tau q)
      hprojection E
  change restrictVector (Function.Embedding.refl A) projection
      (EscapeCount.diagonal tau E) =
    EscapeCount.diagonal (quotientUpdate tau q)
      (restrictTable (Function.Embedding.refl A) projection E)
  exact h

-- Unit data witnesses that the quantified domain is inhabited.
example :
    (fun a : Unit =>
      (@Quotient.mk'' Unit (Setoid.ker (completeItinerary id id)))
        (EscapeCount.diagonal id (fun _ _ => ()) a)) =
      EscapeCount.diagonal (quotientUpdate id id)
        (fun _ _ =>
          (@Quotient.mk'' Unit (Setoid.ker (completeItinerary id id))) ()) := by
  exact completion_quotient_diagonal_naturality id id (fun _ _ => ())

end D5.S3.ObserverMemory.Prediction.CompletionDiagonalNaturality
