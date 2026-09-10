/- GID: D5/S3/ObserverMemory/FiniteCountermodels/TwoTimeTruthRetention
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/FiniteCountermodels/TwoTimeTruthRetention
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ObserverMemory/FiniteCountermodels/TwoTimeTruthRetention.PersistentTruthAlwaysKnown; result=D5/S3/ObserverMemory/FiniteCountermodels/TwoTimeTruthRetention.persistent_truth_not_always_known; claim=D5/S3/ObserverMemory/FiniteCountermodels/TwoTimeTruthRetention.PersistentTruthAlwaysKnown
   digest: A persistent Boolean event need not remain recoverable from a later readout. -/

import D5.S3.ObserverMemory.TwoTimeKnowledge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.FiniteCountermodels.TwoTimeTruthRetention

open D5.S3.ObserverMemory.TwoTimeKnowledge

/-- The universal no-forgetting claim already restricted to two times and two worlds.
Knowledge means the event value is constant on each readout fiber. -/
def PersistentTruthAlwaysKnown : Prop :=
  ∀ (readout : Bool → Bool → Bool) (value : Unit → Bool → Bool)
    (ledger : Bool → Set Unit) (e : Unit) (t0 t1 : Bool),
    t0 < t1 → Persists ledger e t0 t1 →
      Knows readout value e t0 → Knows readout value e t1

/-- The existing finite forgetting certificate refutes the universal claim, with
ledger persistence and earlier knowledge both supplied by that certificate. -/
theorem persistent_truth_not_always_known : ¬PersistentTruthAlwaysKnown := by
  intro hretains
  have hforgot := finite_certificate_instantiates_forgot.2.1
  exact hforgot.2.2.2
    (hretains certificateReadout boolEventValue boolLedger () false true
      hforgot.1 hforgot.2.1 hforgot.2.2.1)

#print axioms persistent_truth_not_always_known

end D5.S3.ObserverMemory.FiniteCountermodels.TwoTimeTruthRetention
