/- GID: D5/S3/ObserverMemory/PredictionCertificates/LocalCertificateCanonicalMinimality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/LocalCertificateCanonicalMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Local distance certificates expose the canonical predictive equivalence and unique quotient update. -/

import D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

namespace D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateCanonicalMinimality

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
open D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality
open Filter

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Local distance and fibre checks expose the canonical predictive equivalence,
the uniquely determined quotient update, exact depth, state-count minimality,
and quadratic verification work. -/
theorem local_certificate_canonical_minimality
    {Y O C : Type*} [Fintype Y] [Fintype C]
    (tau : Y -> Y) (q : Y -> O) (label : Y -> C)
    (delta : Y -> Y -> Option Nat)
    (label_surjective : Function.Surjective label)
    (fiber_check : ∀ y y', label y = label y' ↔ delta y y' = none)
    (distance_checks : LocalDistanceChecks tau q delta) :
    (∀ y y', label y = label y' ↔
      completeItinerary tau q y = completeItinerary tau q y') ∧
    (∃! quotientUpdate : C -> C,
      ∀ y, quotientUpdate (label y) = label (tau y)) ∧
    (∃ equiv : C ≃ PredictiveCompletion tau q,
      ∀ y y', equiv (label y) = equiv (label y') ↔
        completeItinerary tau q y = completeItinerary tau q y') ∧
    certificateDepth delta = stabilityDepth tau q ∧
    MinimalStateCount tau q C ∧
    (fun n : Nat => certificateCheckWork n) =O[atTop]
      (fun n : Nat => (n : Real) ^ 2) := by
  have h := local_certificate_global_minimality tau q label delta
    label_surjective fiber_check distance_checks
  rcases h with ⟨hclasses, hupdate, _, hdepth, hminimal, hwork⟩
  have hupdate_unique : ∃! quotientUpdate : C -> C,
      ∀ y, quotientUpdate (label y) = label (tau y) := by
    rcases hupdate with ⟨quotientUpdate, hquotientUpdate⟩
    refine ⟨quotientUpdate, hquotientUpdate, ?_⟩
    intro other hother
    funext state
    obtain ⟨y, hy⟩ := label_surjective state
    calc
      other state = other (label y) := congrArg other hy.symm
      _ = label (tau y) := hother y
      _ = quotientUpdate (label y) := (hquotientUpdate y).symm
      _ = quotientUpdate state := congrArg quotientUpdate hy
  let equiv : C ≃ PredictiveCompletion tau q :=
    quotientEquivOfExactKernel label (completeItinerary tau q)
      label_surjective hclasses
  have hequiv_property : ∀ y y', equiv (label y) = equiv (label y') ↔
      completeItinerary tau q y = completeItinerary tau q y' := by
    intro y y'
    constructor
    · intro h
      exact (hclasses y y').mp (equiv.injective h)
    · intro h
      exact congrArg equiv ((hclasses y y').mpr h)
  exact ⟨hclasses, hupdate_unique, ⟨equiv, hequiv_property⟩,
    hdepth, hminimal, hwork⟩

#print axioms local_certificate_canonical_minimality

end D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateCanonicalMinimality
