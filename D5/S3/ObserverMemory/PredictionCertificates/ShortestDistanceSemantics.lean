/- GID: D5/S3/ObserverMemory/PredictionCertificates/ShortestDistanceSemantics
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/ShortestDistanceSemantics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: First-mismatch distance exactly measures future separation and stable depth. -/

import D5.S3.Observer.Separation.FiniteHistoryStability
import D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

/- Library-search audit trail (2026-08-24):
   * Exact family hits `shortestDistance`, `FirstMismatch`, `stabilityDepth`, and
     `shortest_distance_eq_none_iff` provide the canonical extended distance,
     its source-level first-mismatch test, its finite maximum, and its infinity
     criterion; they are imported rather than redeclared.
   * Exact family hits `observationStabilityDepth` and
     `finite_history_stability` provide the canonical least stable horizon and
     identify its finite relation with the complete-future relation.
   * Pinned Mathlib exact hits `Nat.find_spec`, `Nat.find_min`, `Nat.sInf_le`,
     `Finset.le_sup`, and `Finset.sup_le` supply least-witness and finite-maximum
     steps. Repository and pinned-Mathlib searches found no theorem identifying
     the two canonical depth objects or packaging all five public clauses.
   * `loogle` and `leansearch` executables are absent from PATH on this lane. -/

namespace D5.S3.ObserverMemory.PredictionCertificates.ShortestDistanceSemantics

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.Observer.Separation.FiniteHistoryStability
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private theorem first_mismatch_iff_observed
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (first second : Y) (depth : Nat) :
    FirstMismatch update readout first second depth ↔
      observedAt update readout depth first ≠
          observedAt update readout depth second ∧
        ∀ earlier, earlier < depth ->
          observedAt update readout earlier first =
            observedAt update readout earlier second := by
  induction depth generalizing first second with
  | zero =>
      simp [FirstMismatch, observedAt]
  | succ depth ih =>
      constructor
      · rintro ⟨hcurrent, hnext⟩
        have hnextSemantics :=
          (ih (update first) (update second)).mp hnext
        refine ⟨?_, ?_⟩
        · simpa [observedAt, Function.iterate_succ_apply] using
            hnextSemantics.1
        · intro earlier hearlier
          cases earlier with
          | zero => simpa [observedAt] using hcurrent
          | succ earlier =>
              have hlt : earlier < depth :=
                Nat.lt_of_succ_lt_succ hearlier
              simpa [observedAt, Function.iterate_succ_apply] using
                hnextSemantics.2 earlier hlt
      · rintro ⟨hmismatch, hearlier⟩
        refine ⟨?_, (ih (update first) (update second)).mpr ⟨?_, ?_⟩⟩
        · simpa [observedAt] using hearlier 0 (Nat.zero_lt_succ depth)
        · simpa [observedAt, Function.iterate_succ_apply] using hmismatch
        · intro earlier hlt
          simpa [observedAt, Function.iterate_succ_apply] using
            hearlier (earlier + 1) (Nat.succ_lt_succ hlt)

private theorem shortest_distance_some_iff
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (pair : Y × Y) (depth : Nat) :
    shortestDistance update readout pair.1 pair.2 = some depth ↔
      observedAt update readout depth pair.1 ≠
          observedAt update readout depth pair.2 ∧
        ∀ earlier, earlier < depth ->
          observedAt update readout earlier pair.1 =
            observedAt update readout earlier pair.2 := by
  classical
  rw [shortestDistance]
  split_ifs with hexists
  · simp only [Option.some.injEq]
    constructor
    · intro hfind
      apply (first_mismatch_iff_observed update readout pair.1 pair.2 depth).mp
      simpa [hfind] using Nat.find_spec hexists
    · intro hsemantics
      apply Nat.find_eq_iff hexists |>.2
      refine ⟨
        (first_mismatch_iff_observed update readout pair.1 pair.2 depth).mpr
          hsemantics, ?_⟩
      intro earlier hearlier hfirst
      have hmismatch :=
        (first_mismatch_iff_observed update readout pair.1 pair.2 earlier).mp
          hfirst |>.1
      exact hmismatch (hsemantics.2 earlier hearlier)
  · simp only [false_iff]
    intro hsemantics
    exact hexists ⟨depth,
      (first_mismatch_iff_observed update readout pair.1 pair.2 depth).mpr
        hsemantics⟩

private theorem shortest_distance_isSome_iff
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (pair : Y × Y) :
    (shortestDistance update readout pair.1 pair.2).isSome ↔
      ∃ depth, observedAt update readout depth pair.1 ≠
        observedAt update readout depth pair.2 := by
  classical
  constructor
  · intro hsome
    cases hdistance : shortestDistance update readout pair.1 pair.2 with
    | none => simp [hdistance] at hsome
    | some depth =>
        exact ⟨depth,
          ((shortest_distance_some_iff update readout pair depth).mp
            hdistance).1⟩
  · rintro ⟨witness, hwitness⟩
    let separates : Nat -> Prop := fun depth =>
      observedAt update readout depth pair.1 ≠
        observedAt update readout depth pair.2
    have hexists : ∃ depth, separates depth := ⟨witness, hwitness⟩
    have hleast :
        observedAt update readout (Nat.find hexists) pair.1 ≠
            observedAt update readout (Nat.find hexists) pair.2 ∧
          ∀ earlier, earlier < Nat.find hexists ->
            observedAt update readout earlier pair.1 =
              observedAt update readout earlier pair.2 := by
      refine ⟨Nat.find_spec hexists, ?_⟩
      intro earlier hearlier
      exact of_not_not (Nat.find_min hexists hearlier)
    have hdistance : shortestDistance update readout pair.1 pair.2 =
        some (Nat.find hexists) :=
      (shortest_distance_some_iff update readout pair (Nat.find hexists)).mpr
        hleast
    simp [hdistance]

private theorem shortest_distance_none_iff_infinite_relation
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (pair : Y × Y) :
    shortestDistance update readout pair.1 pair.2 = none ↔
      pair ∈ infiniteFutureRelation update readout := by
  rw [shortest_distance_eq_none_iff]
  constructor
  · intro hitinerary depth
    simpa [completeItinerary, observedAt] using congrFun hitinerary depth
  · intro hfuture
    funext depth
    simpa [completeItinerary, observedAt] using hfuture depth

private theorem observation_setoid_rel_iff
    {Y O : Type*} (update : Y -> Y) (readout : Y -> O)
    (depth : Nat) (first second : Y) :
    observationSetoid update readout depth first second ↔
      (first, second) ∈ finiteFutureRelation update readout depth := by
  constructor
  · intro hword k hk
    simpa only [futureReadoutWord, observedAt] using
      congrFun hword (show Fin (depth + 1) from
        ⟨k, Nat.lt_succ_of_le hk⟩)
  · intro hfuture
    funext k
    simpa only [futureReadoutWord, observedAt] using
      hfuture k (Nat.le_of_lt_succ k.isLt)

private theorem observation_stability_depth_eq_distance_sup
    {Y O : Type*} [Fintype Y]
    (update : Y -> Y) (readout : Y -> O) :
    observationStabilityDepth update readout =
      Finset.univ.sup fun pair : Y × Y =>
        (shortestDistance update readout pair.1 pair.2).getD 0 := by
  classical
  let latest := Finset.univ.sup fun pair : Y × Y =>
    (shortestDistance update readout pair.1 pair.2).getD 0
  have hfinite := finite_history_stability update readout
  have hdepthRelation :
      finiteFutureRelation update readout
          (observationStabilityDepth update readout) =
        infiniteFutureRelation update readout :=
    hfinite.2.2.1
  have hlatestLeDepth : latest ≤ observationStabilityDepth update readout := by
    apply Finset.sup_le
    intro pair _
    cases hdistance : shortestDistance update readout pair.1 pair.2 with
    | none => simp
    | some depth =>
        simp only [Option.getD_some]
        by_contra hnotle
        have hdepthLt : observationStabilityDepth update readout < depth :=
          Nat.lt_of_not_ge hnotle
        have hsemantics :=
          (shortest_distance_some_iff update readout pair depth).mp hdistance
        have hfinitePair : pair ∈ finiteFutureRelation update readout
            (observationStabilityDepth update readout) := by
          intro earlier hearlier
          exact hsemantics.2 earlier (lt_of_le_of_lt hearlier hdepthLt)
        have hinfinitePair : pair ∈ infiniteFutureRelation update readout := by
          rw [← hdepthRelation]
          exact hfinitePair
        exact hsemantics.1 (hinfinitePair depth)
  have hlatestRelation : finiteFutureRelation update readout latest =
      infiniteFutureRelation update readout := by
    apply le_antisymm
    · intro pair hprefix depth
      by_contra hmismatch
      let separates : Nat -> Prop := fun n =>
        observedAt update readout n pair.1 ≠
          observedAt update readout n pair.2
      have hexists : ∃ n, separates n := ⟨depth, hmismatch⟩
      have hleast :
          observedAt update readout (Nat.find hexists) pair.1 ≠
              observedAt update readout (Nat.find hexists) pair.2 ∧
            ∀ earlier, earlier < Nat.find hexists ->
              observedAt update readout earlier pair.1 =
                observedAt update readout earlier pair.2 := by
        refine ⟨Nat.find_spec hexists, ?_⟩
        intro earlier hearlier
        exact of_not_not (Nat.find_min hexists hearlier)
      have hdistance : shortestDistance update readout pair.1 pair.2 =
          some (Nat.find hexists) :=
        (shortest_distance_some_iff update readout pair (Nat.find hexists)).mpr
          hleast
      have hle : Nat.find hexists ≤ latest := by
        have hsup := Finset.le_sup
          (s := Finset.univ)
          (f := fun candidate : Y × Y =>
            (shortestDistance update readout candidate.1 candidate.2).getD 0)
          (Finset.mem_univ pair)
        simpa [latest, hdistance] using hsup
      exact hleast.1 (hprefix (Nat.find hexists) hle)
    · intro pair hfuture depth _
      exact hfuture depth
  have hnextRelation : finiteFutureRelation update readout (latest + 1) =
      infiniteFutureRelation update readout := by
    apply le_antisymm
    · intro pair hnext
      rw [← hlatestRelation]
      intro depth hdepth
      exact hnext depth (hdepth.trans (Nat.le_succ latest))
    · intro pair hfuture depth _
      exact hfuture depth
  have hsetoidStable : observationSetoid update readout latest =
      observationSetoid update readout (latest + 1) := by
    apply Setoid.ext
    intro first second
    rw [observation_setoid_rel_iff, observation_setoid_rel_iff,
      hlatestRelation, hnextRelation]
  have hdepthLeLatest : observationStabilityDepth update readout ≤ latest := by
    exact Nat.sInf_le hsetoidStable
  change observationStabilityDepth update readout = latest
  exact le_antisymm hdepthLeLatest hlatestLeDepth

/-- For a finite deterministic system, the canonical extended distance is
finite exactly for a future-distinguishable pair, its finite value is the first
mismatch time, infinity is complete-future equivalence, and the least stable
horizon is the largest finite distance (zero when no pair is distinguishable). -/
theorem shortest_distance_exact_semantics
    {Y O : Type*} [Fintype Y] [Nonempty Y]
    (update : Y -> Y) (readout : Y -> O) :
    (∀ pair : Y × Y,
      (shortestDistance update readout pair.1 pair.2).isSome ↔
        ∃ depth, observedAt update readout depth pair.1 ≠
          observedAt update readout depth pair.2) ∧
    (∀ (pair : Y × Y) (depth : Nat),
      shortestDistance update readout pair.1 pair.2 = some depth ↔
        observedAt update readout depth pair.1 ≠
            observedAt update readout depth pair.2 ∧
          ∀ earlier, earlier < depth ->
            observedAt update readout earlier pair.1 =
              observedAt update readout earlier pair.2) ∧
    (∀ pair : Y × Y,
      shortestDistance update readout pair.1 pair.2 = none ↔
        pair ∈ infiniteFutureRelation update readout) ∧
    observationStabilityDepth update readout =
      (Finset.univ.sup fun pair : Y × Y =>
        (shortestDistance update readout pair.1 pair.2).getD 0) ∧
    ((∀ pair : Y × Y,
      shortestDistance update readout pair.1 pair.2 = none) ->
        observationStabilityDepth update readout = 0) := by
  refine ⟨shortest_distance_isSome_iff update readout,
    shortest_distance_some_iff update readout,
    shortest_distance_none_iff_infinite_relation update readout,
    observation_stability_depth_eq_distance_sup update readout, ?_⟩
  intro hnone
  rw [observation_stability_depth_eq_distance_sup update readout]
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro pair _
  rw [hnone pair]
  rfl

example : Fintype Bool := inferInstance

example : Nonempty Bool := inferInstance

#print axioms shortest_distance_exact_semantics

end

end D5.S3.ObserverMemory.PredictionCertificates.ShortestDistanceSemantics
