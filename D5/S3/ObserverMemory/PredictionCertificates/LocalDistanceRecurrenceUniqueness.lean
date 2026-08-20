/- GID: D5/S3/ObserverMemory/PredictionCertificates/LocalDistanceRecurrenceUniqueness
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/LocalDistanceRecurrenceUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The local recurrence uniquely fixes the first-mismatch distance. -/

import D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

/- Library-search audit trail (2026-08-20):
   * Exact repository hit `local_distance_eq_shortest` states the full recurrence-uniqueness
     result and is applied directly below.
   * Pinned Mathlib grep for `FirstMismatch`, `Option.map Nat.succ`, and a `Nat.find`
     first-mismatch recurrence theorem found no equal result.
   * The imported definitions construct the local checks from readout equality and transition,
     and construct the canonical distance from the least source-level first mismatch. -/

namespace D5.S3.ObserverMemory.PredictionCertificates.LocalDistanceRecurrenceUniqueness

open D5.S3.ObserverMemory.PredictionCertificates.LocalCertificateMinimality

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every extended-natural distance table satisfying the local three-way recurrence is the
canonical shortest first-mismatch table. -/
theorem local_recurrence_uniquely_determines_shortest_distance
    {Y O : Type*} (step : Y -> Y) (readout : Y -> O)
    (distance : Y -> Y -> Option Nat)
    (checks : LocalDistanceChecks step readout distance) :
    distance = fun y y' => shortestDistance step readout y y' := by
  exact local_distance_eq_shortest step readout distance checks

#print axioms local_recurrence_uniquely_determines_shortest_distance

end D5.S3.ObserverMemory.PredictionCertificates.LocalDistanceRecurrenceUniqueness
