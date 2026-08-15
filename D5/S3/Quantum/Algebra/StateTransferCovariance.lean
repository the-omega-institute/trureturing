/- GID: D5/S3/Quantum/Algebra/StateTransferCovariance
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/StateTransferCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pointwise reads intertwine finite-state pushforwards with pulled-back observables. -/

import D5.S3.Quantum.ObserverAlgebra
import Mathlib.LinearAlgebra.Finsupp.Pi

/- Library-search audit trail (2026-08-15):
   * Loogle and LeanSearch found `FunOnFinite.map` and its exact fiber-sum formula
     `FunOnFinite.map_apply_apply`, but no complete covariance theorem.
   * `Finset.mul_sum` is imported and applied to distribute the observable value
     over the fiber sum; repository and digestion searches found no duplicate. -/

namespace D5.S3.Quantum.Algebra.StateTransferCovariance

open D5.S3.Quantum.ObserverAlgebra

/-- Multiplication by an observable after a finite-state pushforward equals the
pushforward after multiplication by the pulled-back observable. -/
theorem diagonal_state_transfer_covariance
    {Y : Type*} [Finite Y]
    (tau : Y → Y) (f : Y → Complex) :
    readObservable f ∘ FunOnFinite.map tau =
      FunOnFinite.map tau ∘ readObservable (f ∘ tau) := by
  classical
  letI := Fintype.ofFinite Y
  funext psi z
  simp only [Function.comp_apply, readObservable, FunOnFinite.map_apply_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have htau : tau y = z := (Finset.mem_filter.mp hy).2
  rw [htau]

-- A concrete finite register witnesses that the statement is inhabited.
example :
    readObservable (fun _ : Unit => (2 : Complex)) ∘
        FunOnFinite.map (id : Unit → Unit) =
      FunOnFinite.map (id : Unit → Unit) ∘
        readObservable ((fun _ : Unit => (2 : Complex)) ∘ (id : Unit → Unit)) := by
  exact diagonal_state_transfer_covariance (id : Unit → Unit)
    (fun _ : Unit => (2 : Complex))

end D5.S3.Quantum.Algebra.StateTransferCovariance
