/- GID: D5/S3/ObserverMemory/PredictionCertificates/EarliestFutureWitness
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/EarliestFutureWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Memory records the earliest future readout mismatch of currently merged states. -/

import D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

/- Library-search audit trail (2026-08-25):
   * Exact family hits `FirstMismatch`, `shortestDistance`, and
     `completeItinerary` construct the source's recursive mismatch test,
     canonical least distance, and future readout trajectory.
   * The finite packaged theorem `shortest_distance_exact_semantics` has the
     mismatch clause but adds `[Fintype Y] [Nonempty Y]`, so it is not an exact
     same-generality hit for this result.
   * Pinned Mathlib hits `Nat.find_spec`, `Nat.find_min`, and `Nat.find_eq_iff`
     supply the least-witness steps. No general packaged theorem was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionCertificates.EarliestFutureWitness

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

/-- If two states have the same current readout, their finite canonical memory
distance is exactly a positive earliest future mismatch: the readouts differ at
that time and agree at every earlier time. -/
theorem memory_is_earliest_future_witness
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (first second : Y) (depth : Nat)
    (currently_equal : readout first = readout second) :
    shortestDistance update readout first second = some depth ↔
      0 < depth /\
      completeItinerary update readout first depth ≠
        completeItinerary update readout second depth /\
      forall earlier, earlier < depth ->
        completeItinerary update readout first earlier =
          completeItinerary update readout second earlier := by
  classical
  have first_mismatch_semantics :
      forall (left right : Y) (n : Nat),
        FirstMismatch update readout left right n ↔
          completeItinerary update readout left n ≠
              completeItinerary update readout right n /\
            forall earlier, earlier < n ->
              completeItinerary update readout left earlier =
                completeItinerary update readout right earlier := by
    intro left right n
    induction n generalizing left right with
    | zero =>
        simp [FirstMismatch, completeItinerary]
    | succ n ih =>
        constructor
        · rintro ⟨hcurrent, hnext⟩
          have hnext_semantics := (ih (update left) (update right)).mp hnext
          refine ⟨?_, ?_⟩
          · simpa [completeItinerary, Function.iterate_succ_apply] using
              hnext_semantics.1
          · intro earlier hearlier
            cases earlier with
            | zero => simpa [completeItinerary] using hcurrent
            | succ earlier =>
                have hlt : earlier < n := Nat.lt_of_succ_lt_succ hearlier
                simpa [completeItinerary, Function.iterate_succ_apply] using
                  hnext_semantics.2 earlier hlt
        · rintro ⟨hmismatch, hearlier⟩
          refine ⟨?_, (ih (update left) (update right)).mpr ⟨?_, ?_⟩⟩
          · simpa [completeItinerary] using hearlier 0 (Nat.zero_lt_succ n)
          · simpa [completeItinerary, Function.iterate_succ_apply] using hmismatch
          · intro earlier hlt
            simpa [completeItinerary, Function.iterate_succ_apply] using
              hearlier (earlier + 1) (Nat.succ_lt_succ hlt)
  rw [shortestDistance]
  split_ifs with hexists
  · simp only [Option.some.injEq]
    constructor
    · intro hfind
      have hfirst : FirstMismatch update readout first second depth := by
        simpa [hfind] using Nat.find_spec hexists
      have hsemantics :=
        (first_mismatch_semantics first second depth).mp hfirst
      have hdepth : 0 < depth := by
        by_contra hnot
        have hzero : depth = 0 := Nat.eq_zero_of_not_pos hnot
        exact hsemantics.1 (by
          simpa [hzero, completeItinerary] using currently_equal)
      exact ⟨hdepth, hsemantics⟩
    · rintro ⟨_hpositive, hmismatch, hearlier⟩
      apply Nat.find_eq_iff hexists |>.2
      refine ⟨(first_mismatch_semantics first second depth).mpr
        ⟨hmismatch, hearlier⟩, ?_⟩
      intro earlier hearlier_depth hfirst
      have hearlier_mismatch :=
        (first_mismatch_semantics first second earlier).mp hfirst |>.1
      exact hearlier_mismatch (hearlier earlier hearlier_depth)
  · simp only [false_iff]
    rintro ⟨_hpositive, hmismatch, hearlier⟩
    exact hexists ⟨depth,
      (first_mismatch_semantics first second depth).mpr
        ⟨hmismatch, hearlier⟩⟩

example :
    let update : Fin 3 -> Fin 3 := fun state => if state = 1 then 2 else state
    let readout : Fin 3 -> Bool := fun state => state = 2
    shortestDistance update readout 0 1 = some 1 := by
  dsimp
  apply (memory_is_earliest_future_witness _ _ 0 1 1 (by decide)).mpr
  decide

#print axioms memory_is_earliest_future_witness

end D5.S3.ObserverMemory.PredictionCertificates.EarliestFutureWitness
