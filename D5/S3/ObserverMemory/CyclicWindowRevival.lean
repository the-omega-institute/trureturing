/- GID: D5/S3/ObserverMemory/CyclicWindowRevival
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/CyclicWindowRevival
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A cyclic observer window returns both generators after one full loop. -/

/- Library-search audit trail (2026-08-14):
   * Exact local hits: `D5.S3.Observer.WindowRegister.shiftMatrix_pow_card` and
     `D5.S3.Observer.WindowRegister.clockMatrix_pow_card` prove the two recurrence clauses.
   * Pinned Mathlib has generic finite-order and periodic-point lemmas, including
     `isPeriodicPt_mul_iff_pow_eq_one`, but no theorem for these concrete window generators.
   * Searches for a joint cyclic-window revival theorem found no exact hit in Mathlib or D5.
   * The theorem below is a thin wrapper around the two exact local results.
-/

import D5.S3.Observer.WindowRegister

namespace D5.S3.ObserverMemory.CyclicWindowRevival

/-- After one full cyclic-window loop, both the address shift and phase clock return to the
identity. This certifies the cyclic revival clause only; no golden-branch grading is asserted. -/
theorem cyclic_window_generators_recur (M : Nat) [NeZero M] :
    D5.S3.Observer.WindowRegister.shiftMatrix M ^ M = 1 ∧
      D5.S3.Observer.WindowRegister.clockMatrix M ^ M = 1 := by
  exact ⟨D5.S3.Observer.WindowRegister.shiftMatrix_pow_card,
    D5.S3.Observer.WindowRegister.clockMatrix_pow_card⟩

end D5.S3.ObserverMemory.CyclicWindowRevival
