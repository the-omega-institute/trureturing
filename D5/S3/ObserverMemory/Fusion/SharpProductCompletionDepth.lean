/- GID: D5/S3/ObserverMemory/Fusion/SharpProductCompletionDepth
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Fusion/SharpProductCompletionDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Sharp local witnesses give the maximum law for finite product completion depth. -/

import D5.S3.ObserverMemory.PredictionCertificates.ShortestDistanceSemantics

/- Library-search audit trail (2026-08-25):
   * Exact family hits `futureReadoutWord`, `completeItinerary`, `observedAt`,
     `shortestDistance`, and `observationStabilityDepth` supply the source's
     finite words, full trajectories, point observations, canonical earliest
     mismatch, and least stable horizon; none is redeclared here.
   * Exact family hit `shortest_distance_exact_semantics` identifies the least
     stable horizon with the largest finite earliest mismatch and is applied.
   * The existing independent-product quotient theorem does not state a depth
     law. Repository body-shape searches found no dependent-product depth law.
   * Pinned Mathlib has no exact theorem for this observer construction;
     `Finset.le_sup` and `Finset.sup_le` are supporting finite-order hits. -/

namespace D5.S3.ObserverMemory.Fusion.SharpProductCompletionDepth

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.Observer.Separation.FiniteObservationRefinementBound
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality
open D5.S3.ObserverMemory.PredictionCertificates.ShortestDistanceSemantics

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem pointwise_update_iterate
    {index : Type*} {state : index -> Type*}
    (update : forall i, state i -> state i)
    (configuration : forall i, state i) (depth : Nat) (i : index) :
    ((fun current => fun i => update i (current i))^[depth]) configuration i =
      ((update i)^[depth]) (configuration i) := by
  induction depth generalizing configuration with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]

private theorem pointwise_observed_at
    {index : Type*} {state output : index -> Type*}
    (update : forall i, state i -> state i)
    (readout : forall i, state i -> output i)
    (depth : Nat) (configuration : forall i, state i) (i : index) :
    observedAt (fun current i => update i (current i))
        (fun current i => readout i (current i)) depth configuration i =
      observedAt (update i) (readout i) depth (configuration i) := by
  simp only [observedAt, pointwise_update_iterate]

/-- Positive local depths are sufficient and have witnesses first separated at
that depth, while a zero-depth factor is already completed by its current
readout. For the pointwise independent product, the canonical least completion
depth is exactly the maximum local depth. -/
theorem sharp_product_completion_depth
    {index : Type*} [Fintype index]
    {state output : index -> Type*}
    [Fintype (forall i, state i)] [forall i, Nonempty (state i)]
    (update : forall i, state i -> state i)
    (readout : forall i, state i -> output i)
    (localDepth : index -> Nat)
    (positiveCompletion : forall i, 0 < localDepth i ->
      forall first second,
        futureReadoutWord (update i) (readout i) (localDepth i) first =
            futureReadoutWord (update i) (readout i) (localDepth i) second ->
          completeItinerary (update i) (readout i) first =
            completeItinerary (update i) (readout i) second)
    (sharpWitness : forall i, 0 < localDepth i ->
      exists first second,
        futureReadoutWord (update i) (readout i) (localDepth i - 1) first =
            futureReadoutWord (update i) (readout i) (localDepth i - 1) second /\
          completeItinerary (update i) (readout i) first (localDepth i) ≠
            completeItinerary (update i) (readout i) second (localDepth i))
    (zeroCompletion : forall i, localDepth i = 0 ->
      forall first second, readout i first = readout i second ->
        completeItinerary (update i) (readout i) first =
          completeItinerary (update i) (readout i) second) :
    observationStabilityDepth
        (fun current i => update i (current i))
        (fun current i => readout i (current i)) =
      Finset.univ.sup localDepth := by
  classical
  let globalUpdate : (forall i, state i) -> forall i, state i :=
    fun current i => update i (current i)
  let globalReadout : (forall i, state i) -> forall i, output i :=
    fun current i => readout i (current i)
  let maximum := Finset.univ.sup localDepth
  let globalDistanceMaximum := Finset.univ.sup
    (fun pair : Prod (forall i, state i) (forall i, state i) =>
      (shortestDistance globalUpdate globalReadout pair.1 pair.2).getD 0)
  have globalSemantics :=
    shortest_distance_exact_semantics globalUpdate globalReadout
  have depthAsDistanceMaximum :
      observationStabilityDepth globalUpdate globalReadout =
        globalDistanceMaximum := by
    exact globalSemantics.2.2.2.1
  change observationStabilityDepth globalUpdate globalReadout = maximum
  rw [depthAsDistanceMaximum]
  apply le_antisymm
  · apply Finset.sup_le
    intro pair _
    cases distanceEquation : shortestDistance globalUpdate globalReadout
        pair.1 pair.2 with
    | none => simp
    | some distance =>
        simp only [Option.getD_some]
        have globalFirstMismatch :=
          (globalSemantics.2.1 pair distance).mp distanceEquation
        obtain ⟨i, coordinateMismatch⟩ :=
          Function.ne_iff.mp globalFirstMismatch.1
        have localMismatch :
            observedAt (update i) (readout i) distance (pair.1 i) ≠
              observedAt (update i) (readout i) distance (pair.2 i) := by
          simpa only [globalUpdate, globalReadout, pointwise_observed_at] using
            coordinateMismatch
        have distanceLeLocal : distance <= localDepth i := by
          by_contra hnot
          have localLtDistance : localDepth i < distance :=
            Nat.lt_of_not_ge hnot
          have completeEquality :
              completeItinerary (update i) (readout i) (pair.1 i) =
                completeItinerary (update i) (readout i) (pair.2 i) := by
            by_cases hzero : localDepth i = 0
            · apply zeroCompletion i hzero
              have zeroLtDistance : 0 < distance := by omega
              have currentEquality :=
                congrFun (globalFirstMismatch.2 0 zeroLtDistance) i
              simpa only [globalUpdate, globalReadout, pointwise_observed_at,
                observedAt, Function.iterate_zero_apply] using currentEquality
            · apply positiveCompletion i (Nat.pos_of_ne_zero hzero)
              funext k
              have kLeLocal : (k : Nat) <= localDepth i :=
                Nat.le_of_lt_succ k.isLt
              have kLtDistance : (k : Nat) < distance :=
                lt_of_le_of_lt kLeLocal localLtDistance
              have globalEquality :=
                congrFun (globalFirstMismatch.2 k kLtDistance) i
              change observedAt (update i) (readout i) k (pair.1 i) =
                observedAt (update i) (readout i) k (pair.2 i)
              simpa only [globalUpdate, globalReadout,
                pointwise_observed_at] using globalEquality
          exact localMismatch (by
            simpa only [completeItinerary, observedAt] using
              congrFun completeEquality distance)
        exact distanceLeLocal.trans
          (Finset.le_sup (s := Finset.univ) (f := localDepth)
            (Finset.mem_univ i))
  · apply Finset.sup_le
    intro i _
    by_cases hzero : localDepth i = 0
    · simp [hzero]
    · have hpositive : 0 < localDepth i := Nat.pos_of_ne_zero hzero
      obtain ⟨localFirst, localSecond, sameBefore, differentAtDepth⟩ :=
        sharpWitness i hpositive
      let base : forall j, state j :=
        fun j => Classical.choice (inferInstance : Nonempty (state j))
      let first := Function.update base i localFirst
      let second := Function.update base i localSecond
      have globalMismatch :
          observedAt globalUpdate globalReadout (localDepth i) first ≠
            observedAt globalUpdate globalReadout (localDepth i) second := by
        intro equality
        have coordinateEquality := congrFun equality i
        have localCoordinateEquality :
            observedAt (update i) (readout i) (localDepth i) (first i) =
              observedAt (update i) (readout i) (localDepth i) (second i) := by
          calc
            observedAt (update i) (readout i) (localDepth i) (first i) =
                observedAt globalUpdate globalReadout (localDepth i) first i := by
              symm
              exact pointwise_observed_at update readout
                (localDepth i) first i
            _ = observedAt globalUpdate globalReadout
                (localDepth i) second i := coordinateEquality
            _ = observedAt (update i) (readout i)
                (localDepth i) (second i) :=
              pointwise_observed_at update readout (localDepth i) second i
        apply differentAtDepth
        simpa [completeItinerary, observedAt, first, second,
          Function.update] using localCoordinateEquality
      have globalEarlier : forall earlier, earlier < localDepth i ->
          observedAt globalUpdate globalReadout earlier first =
            observedAt globalUpdate globalReadout earlier second := by
        intro earlier hearlier
        funext j
        by_cases hji : j = i
        · subst j
          have earlierLe : earlier <= localDepth i - 1 := by omega
          have localEquality := congrFun sameBefore
            (show Fin (localDepth i - 1 + 1) from
              ⟨earlier, Nat.lt_succ_of_le earlierLe⟩)
          change observedAt (update i) (readout i) earlier localFirst =
            observedAt (update i) (readout i) earlier localSecond at localEquality
          simpa [globalUpdate, globalReadout, pointwise_observed_at,
            first, second, Function.update] using localEquality
        · simp [globalUpdate, globalReadout, pointwise_observed_at,
            first, second, Function.update, hji]
      have globalDistance :
          shortestDistance globalUpdate globalReadout first second =
            some (localDepth i) :=
        (globalSemantics.2.1 (first, second) (localDepth i)).mpr
          ⟨globalMismatch, globalEarlier⟩
      have belowGlobalMaximum := Finset.le_sup
        (s := Finset.univ)
        (f := fun pair : Prod (forall i, state i) (forall i, state i) =>
          (shortestDistance globalUpdate globalReadout pair.1 pair.2).getD 0)
        (Finset.mem_univ (first, second))
      simpa only [globalDistance, Option.getD_some,
        globalDistanceMaximum] using belowGlobalMaximum

example :
    observationStabilityDepth
        (fun current : Fin 2 -> Fin 2 => current)
        (fun current : Fin 2 -> Fin 2 => current) =
      Finset.univ.sup (fun _ : Fin 2 => 0) := by
  apply sharp_product_completion_depth
    (update := fun _ value => value)
    (readout := fun _ value => value)
    (localDepth := fun _ : Fin 2 => 0)
  · intro i hpositive
    omega
  · intro i hpositive
    omega
  · intro i _ first second currentEquality
    funext depth
    change ((id : Fin 2 -> Fin 2)^[depth]) first =
      ((id : Fin 2 -> Fin 2)^[depth]) second
    rw [Function.iterate_id]
    exact currentEquality

#print axioms sharp_product_completion_depth

end D5.S3.ObserverMemory.Fusion.SharpProductCompletionDepth
