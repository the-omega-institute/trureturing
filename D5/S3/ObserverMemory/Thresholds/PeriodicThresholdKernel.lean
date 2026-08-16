/- GID: D5/S3/ObserverMemory/Thresholds/PeriodicThresholdKernel
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Thresholds/PeriodicThresholdKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reachable periodic states exactly control eventual threshold bounds. -/

import D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
import Mathlib.Dynamics.PeriodicPts.Defs

/- Library-search audit trail (2026-08-16):
   * Repository search found the strictly weaker quantitative theorem
     `finite_orbit_and_readout_eventually_periodic`; it is imported and applied below.
   * Pinned-Mathlib search found `Function.mem_periodicPts`,
     `Function.IsPeriodicPt.mul_const`, and `Function.iterate_add_apply`; no declaration
     states the full equivalence between an eventual threshold and the reachable periodic core.
   * Three local `smart_search.sh` queries returned no full-statement match.
   * The NyxID service catalog exposed no Loogle or LeanSearch connection. Two GitHub code-search
     proxy requests failed with HTTP 400 (`API key is failed`), so they supplied no conclusion. -/

namespace D5.S3.ObserverMemory.Thresholds.PeriodicThresholdKernel

open D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound

/-- The periodic states that occur on an orbit starting in `A`. -/
def reachablePeriodicStates {Y : Type*} (F : Y -> Y) (A : Set Y) : Set Y :=
  {p | p ∈ Function.periodicPts F ∧ ∃ a ∈ A, ∃ n : Nat, (F^[n]) a = p}

/-- On a finite deterministic system, an observable is eventually bounded by a threshold,
uniformly over all initial states in `A`, exactly when it is bounded on every reachable periodic
state. -/
theorem eventual_threshold_iff_reachable_periodic
    {Y : Type*} [Finite Y] (F : Y -> Y) (A : Set Y)
    (value : Y -> ℝ) (threshold : ℝ) :
    (∃ N : Nat, ∀ a ∈ A, ∀ t : Nat, N ≤ t -> value ((F^[t]) a) ≤ threshold) ↔
      ∀ p ∈ reachablePeriodicStates F A, value p ≤ threshold := by
  letI := Fintype.ofFinite Y
  constructor
  · rintro ⟨N, hEventually⟩ p ⟨hPeriodic, a, ha, n, hn⟩
    rw [Function.mem_periodicPts] at hPeriodic
    obtain ⟨period, hperiod_pos, hperiod⟩ := hPeriodic
    have htime : N ≤ period * N + n :=
      (Nat.le_mul_of_pos_left N hperiod_pos).trans (Nat.le_add_right _ _)
    have hvalue := hEventually a ha (period * N + n) htime
    have horbit : (F^[period * N + n]) a = p := by
      rw [Function.iterate_add_apply, hn]
      exact hperiod.mul_const N
    rw [horbit] at hvalue
    exact hvalue
  · intro hPeriodic
    refine ⟨Fintype.card Y, ?_⟩
    intro a ha t ht
    obtain ⟨mu, period, hperiod_pos, hbound, htail⟩ :=
      finite_orbit_and_readout_eventually_periodic F (fun _ : Y => Unit.unit) a
    have hmu : mu ≤ t := by omega
    apply hPeriodic ((F^[t]) a)
    constructor
    · rw [Function.mem_periodicPts]
      refine ⟨period, hperiod_pos, ?_⟩
      change (F^[period]) ((F^[t]) a) = (F^[t]) a
      rw [← Function.iterate_add_apply, Nat.add_comm]
      exact (htail t hmu).1
    · exact ⟨a, ha, t, rfl⟩

#print axioms eventual_threshold_iff_reachable_periodic

end D5.S3.ObserverMemory.Thresholds.PeriodicThresholdKernel
