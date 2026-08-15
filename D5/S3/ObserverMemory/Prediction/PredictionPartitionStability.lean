/- GID: D5/S3/ObserverMemory/Prediction/PredictionPartitionStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Prediction/PredictionPartitionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equality of consecutive prediction partitions makes every later partition equal. -/

import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/- Library-search audit trail (2026-08-16):
   * Repository search found the finite readout-word definition below, but no
     theorem asserting both update congruence and permanent partition stability.
   * Pinned Mathlib search found no theorem with the full statement shape.
   * Pinned Mathlib and Loogle exactly found `Function.iterate_add_apply`; the
     proof imports and applies it to align shifted readout coordinates.
   * LeanSearch's shaped search endpoint returned HTTP 404 and no result. -/

namespace D5.S3.ObserverMemory.Prediction.PredictionPartitionStability

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

/-- If equality of readout words through `m` is exactly equality through
`m + 1`, then the depth-`m` relation is preserved by the update and every
later finite readout relation is the same relation. -/
theorem prediction_partition_stable_forever {Y O : Type*}
    (F : Y -> Y) (q : Y -> O) (m : Nat)
    (hstep : forall y y',
      futureReadoutWord F q m y = futureReadoutWord F q m y' <->
        futureReadoutWord F q (m + 1) y =
          futureReadoutWord F q (m + 1) y') :
    (forall y y',
      futureReadoutWord F q m y = futureReadoutWord F q m y' ->
        futureReadoutWord F q m (F y) = futureReadoutWord F q m (F y')) /\
    (forall r y y',
      futureReadoutWord F q (m + r) y = futureReadoutWord F q (m + r) y' <->
        futureReadoutWord F q m y = futureReadoutWord F q m y') := by
  have preserves : forall {y y'},
      futureReadoutWord F q m y = futureReadoutWord F q m y' ->
        futureReadoutWord F q m (F y) = futureReadoutWord F q m (F y') := by
    intro y y' heq
    have hnext := (hstep y y').mp heq
    funext k
    have hcoordinate := congrFun hnext
      (show Fin (m + 1 + 1) from ⟨k + 1, by omega⟩)
    simpa only [futureReadoutWord, Function.iterate_add_apply,
      Function.iterate_one] using hcoordinate
  refine ⟨?_, ?_⟩
  · intro y y' heq
    exact preserves heq
  · intro r y y'
    constructor
    · intro hlong
      funext k
      have hcoordinate := congrFun hlong
        (show Fin (m + r + 1) from ⟨k, by omega⟩)
      simpa only [futureReadoutWord] using hcoordinate
    · intro heq
      have hiterate : forall n,
          futureReadoutWord F q m ((F^[n]) y) =
            futureReadoutWord F q m ((F^[n]) y') := by
        intro n
        induction n with
        | zero => simpa using heq
        | succ n ih =>
            have hnext := preserves ih
            simpa only [Function.iterate_succ_apply'] using hnext
      funext k
      have hzero := congrFun (hiterate k) (0 : Fin (m + 1))
      simpa [futureReadoutWord] using hzero

/- A constant Boolean readout witnesses that the stabilization hypothesis is
satisfiable on an inhabited, nontrivial state type. -/
example : forall y y' : Bool,
    futureReadoutWord Bool.not (fun _ => false) 0 y =
        futureReadoutWord Bool.not (fun _ => false) 0 y' <->
      futureReadoutWord Bool.not (fun _ => false) (0 + 1) y =
        futureReadoutWord Bool.not (fun _ => false) (0 + 1) y' := by
  intro y y'
  constructor <;> intro _ <;> rfl

#print axioms prediction_partition_stable_forever

end D5.S3.ObserverMemory.Prediction.PredictionPartitionStability
