/- GID: D5/S3/Quantum/ObserverCommutator
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compute the represented observer read-update commutator. -/

import D5.S3.Quantum.ObserverAlgebra

namespace D5.S3.Quantum.ObserverCommutator

open D5.S3.Quantum.ObserverAlgebra

/-- In the register representation, the read-update commutator is the translated
observable difference multiplied by the updated register. -/
theorem observer_read_update_commutator_formula {index : Type*}
    (tau : Equiv.Perm index) (f : index -> Complex) (psi : Register index) :
    observerUpdate tau (readObservable f psi) -
        readObservable f (observerUpdate tau psi) =
      fun i => (f (tau.symm i) - f i) * psi (tau.symm i) := by
  funext i
  simp [observerUpdate, readObservable]
  ring

end D5.S3.Quantum.ObserverCommutator
