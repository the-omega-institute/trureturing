/- GID: D5/S3/ObserverMemory/PredictionCertificates/FiniteHistoryPermanentStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionCertificates/FiniteHistoryPermanentStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equality at consecutive finite-history depths makes every later relation equal. -/

import D5.S3.ObserverMemory.PredictionCertificates.OneStepPermanentStability

/- Library-search audit trail (2026-08-23):
   * Exact repository hit `one_step_stability_is_permanent`, through its canonical
     `futureReadoutWord` objects, has the same consecutive-depth hypothesis and
     all-later-depth conclusion. It is imported and applied directly below.
   * Exact atom-id search outside the digestion ledger and source documentation missed.
   * Related finite-carrier stabilization results add irrelevant finiteness assumptions.
   * Pinned Mathlib searches for one-step permanence of relation-valued histories missed;
     the imported exact hit records and uses `Function.iterate_add_apply`. -/

namespace D5.S3.ObserverMemory.PredictionCertificates.FiniteHistoryPermanentStability

open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.PredictionCertificates.OneStepPermanentStability

/-- Equality of consecutive finite-history relations forces equality between the
depth-`m` relation and the relation at every later depth `m + r`. -/
theorem finite_history_relation_stable_forever {Y O : Type*}
    (update : Y -> Y) (readout : Y -> O) (m : Nat)
    (hstep : forall y y',
      futureReadoutWord update readout m y =
          futureReadoutWord update readout m y' <->
        futureReadoutWord update readout (m + 1) y =
          futureReadoutWord update readout (m + 1) y') :
    forall r y y',
      futureReadoutWord update readout m y =
          futureReadoutWord update readout m y' <->
        futureReadoutWord update readout (m + r) y =
          futureReadoutWord update readout (m + r) y' := by
  intro r y y'
  exact (one_step_stability_is_permanent update readout m hstep).2 r y y' |>.symm

#print axioms finite_history_relation_stable_forever

end D5.S3.ObserverMemory.PredictionCertificates.FiniteHistoryPermanentStability
