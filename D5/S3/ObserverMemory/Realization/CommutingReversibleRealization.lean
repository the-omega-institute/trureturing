/- GID: D5/S3/ObserverMemory/Realization/CommutingReversibleRealization
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Realization/CommutingReversibleRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Commuting realizations have exact itinerary capacity and a reversible-shift criterion. -/

import D5.S3.ObserverMemory.Realization.CanonicalMinimalRealization
import D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
import D5.S3.ObserverMemory.Refinement.GradedPredictionShift
import D5.S3.ObserverMemory.Trajectories.FutureItineraryShift

namespace D5.S3.ObserverMemory.Realization.CommutingReversibleRealization

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Realization.CanonicalMinimalRealization
open D5.S3.ObserverMemory.Realization.FreeWindowRealizationCapacity
open D5.S3.ObserverMemory.Refinement.GradedPredictionShift
open D5.S3.ObserverMemory.Trajectories.FutureItineraryShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

/-- For a nonempty finite source and finite alphabet, commutation upgrades any
finite-window contract to exact prediction at every time. Every finite carrier
has at least as many states as the complete itinerary range. The range itself,
with tail shift and first-coordinate readout, attains this bound with surjective
preparation. A reversible commuting realization exists exactly when tail shift
is injective (equivalently bijective), and the same construction then attains
the reversible minimum. The complete and finite-word counts agree exactly at
stabilization of two consecutive word kernels. -/
theorem commuting_reversible_realization
    {S A : Type u} [Finite S] [Nonempty S] [Finite A]
    (D : S → S) (q : S → A) (n : ℕ) :
    let T := ItineraryRange D q
    let ι : S → T := Set.rangeFactorization (completeItinerary D q)
    let σ := itineraryUpdate D q
    let gT : T → A := fun t => t.1 0
    (∀ (M : Type u) [Finite M] (I : S → M) (F : M → M) (g : M → A),
      (∀ s, I (D s) = F (I s)) → WindowCorrect D q n I F g →
      (∀ s j, g (F^[j] (I s)) = q (D^[j] s)) ∧
      Nat.card T ≤ Nat.card (Set.range I) ∧
      Nat.card (Set.range I) ≤ Nat.card M ∧
      (Function.Bijective F → Function.Bijective σ)) ∧
    (Finite T ∧ Function.Surjective ι ∧
      (∀ s, ι (D s) = σ (ι s)) ∧ WindowCorrect D q n ι σ gT) ∧
    ((∃ (M : Type u) (_ : Finite M) (I : S → M) (F : M → M) (g : M → A),
        (∀ s, I (D s) = F (I s)) ∧ WindowCorrect D q n I F g ∧
        Function.Bijective F) ↔ Function.Injective σ) ∧
    (Function.Injective σ ↔ Function.Bijective σ) ∧
    (Nat.card T = Nat.card (FiniteItineraryRange D q n) ↔
      Setoid.ker (futureReadoutWord D q n) =
        Setoid.ker (futureReadoutWord D q (n + 1))) := by
  classical
  dsimp only
  let ι := Set.rangeFactorization (completeItinerary D q)
  let σ := itineraryUpdate D q
  let gT : ItineraryRange D q → A := fun t => t.1 0
  have hι : ∀ s, ι (D s) = σ (ι s) := by
    intro s
    apply Subtype.ext
    exact future_itinerary_shift D q s
  have hcanonical : WindowCorrect D q n ι σ gT := by
    intro s j
    have hiter := (show Function.Semiconj ι D σ from hι).iterate_right j.val s
    change gT (σ^[j.val] (ι s)) = q (D^[j.val] s)
    rw [← hiter]
    rfl
  have hcarrier : ∀ {M : Type u} [Finite M] (I : S → M) (F : M → M) (g : M → A),
      (∀ s, I (D s) = F (I s)) → WindowCorrect D q n I F g →
      (∀ s j, g (F^[j] (I s)) = q (D^[j] s)) ∧
      Nat.card (ItineraryRange D q) ≤ Nat.card (Set.range I) ∧
      Nat.card (Set.range I) ≤ Nat.card M ∧
      (Function.Bijective F → Function.Bijective σ) := by
    intro M _ I F g hc hw
    have hread : ∀ s, q s = g (I s) := fun s => (hw s 0).symm
    obtain ⟨π, hπ, _⟩ := canonical_minimal_realization D q I F g hc hread
    refine ⟨?_, Nat.card_le_card_of_surjective π hπ.1,
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective, ?_⟩
    · intro s j
      rw [← (show Function.Semiconj I D F from hc).iterate_right j s]
      exact (hread _).symm
    · intro hF
      have hinvariant := realization_range_invariant D I F hc
      let U : Set.range I → Set.range I := fun p => ⟨F p.1, hinvariant p⟩
      have hU : Function.Injective U := by
        intro p r heq
        exact Subtype.ext (hF.1 (congrArg Subtype.val heq))
      have honto : Function.Surjective σ := by
        intro t
        obtain ⟨p, hp⟩ := hπ.1 t
        obtain ⟨r, hr⟩ := Finite.surjective_of_injective hU p
        refine ⟨π r, ?_⟩
        calc
          σ (π r) = π (U r) := (congrFun hπ.2.2 r).symm
          _ = π p := congrArg π hr
          _ = t := hp
      exact honto.bijective_of_finite
  refine ⟨fun M _ I F g hc hw => hcarrier I F g hc hw,
    ⟨inferInstance, Set.rangeFactorization_surjective, hι, hcanonical⟩,
    ?_, Finite.injective_iff_bijective, ?_⟩
  · constructor
    · rintro ⟨M, hM, I, F, g, hc, hw, hF⟩
      let := hM
      exact ((hcarrier I F g hc hw).2.2.2 hF).1
    · intro hσ
      exact ⟨ItineraryRange D q, inferInstance, ι, σ, gT, hι, hcanonical,
        hσ.bijective_of_finite⟩
  · constructor
    · intro hcard
      have hprojection : Function.Surjective (coordinateProjection D q n) := by
        rintro ⟨w, s, rfl⟩
        exact ⟨ι s, rfl⟩
      have hinjective :=
        ((Nat.bijective_iff_surjective_and_card (coordinateProjection D q n)).mpr
          ⟨hprojection, hcard⟩).1
      have hker : Setoid.ker (futureReadoutWord D q n) =
          Setoid.ker (completeItinerary D q) := by
        apply Setoid.ext
        intro s t
        constructor
        · intro hword
          exact congrArg Subtype.val (hinjective (show
            coordinateProjection D q n (ι s) = coordinateProjection D q n (ι t)
            from Subtype.ext hword))
        · intro hfull
          exact congrArg (truncateItinerary n) hfull
      apply Setoid.ext
      intro s t
      constructor
      · intro hword
        have hfull := (Setoid.ext_iff.mp hker s t).mp hword
        exact congrArg (truncateItinerary (n + 1)) hfull
      · intro hnext
        exact congrArg (restrictWord (Nat.le_succ n)) hnext
    · intro hstable
      exact (Nat.card_congr
        ((finiteWordRangeEquiv D q n).symm.trans
          ((stableCompletionEquiv D q n hstable).trans
            (Setoid.quotientKerEquivRange (completeItinerary D q))))).symm

#print axioms commuting_reversible_realization

end D5.S3.ObserverMemory.Realization.CommutingReversibleRealization
