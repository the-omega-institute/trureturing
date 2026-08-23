/- GID: D5/S3/ObserverMemory/PredictionCertificates/OneStepPermanentStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/OneStepPermanentStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equality at one consecutive prediction depth makes stability permanent. -/

import D5.S3.ObserverMemory.Prediction.PredictionPartitionStability

/- Library-search audit trail (2026-08-23):
   * Exact repository hit `prediction_partition_stable_forever` has the same
     hypothesis, update-congruence conclusion, and all-later-depth conclusion.
   * It is imported and directly applied below; no part is reproved.
   * No Mathlib search was needed after the exact repository hit. -/

namespace D5.S3.ObserverMemory.PredictionCertificates.OneStepPermanentStability

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Prediction.PredictionPartitionStability

/-- If consecutive finite-readout equality relations agree, the earlier
relation respects the update and equals every later finite-readout relation. -/
theorem one_step_stability_is_permanent {Y O : Type*}
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
  exact prediction_partition_stable_forever F q m hstep

#print axioms one_step_stability_is_permanent

end D5.S3.ObserverMemory.PredictionCertificates.OneStepPermanentStability
