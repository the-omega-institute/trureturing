/- GID: D5/S3/ObserverMemory/Dynamics/FiniteNoFixedPointOrbit
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/FiniteNoFixedPointOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every orbit of a finite fixed-point-free map enters a nontrivial cycle. -/

import D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound
import Mathlib.Tactic

/- Library-search audit trail (2026-08-17):
   * Repository search found the strictly weaker quantitative theorem
     `finite_orbit_and_readout_eventually_periodic`; it is imported and applied directly.
   * Pinned-Mathlib searches found `Fintype.exists_ne_map_eq_of_card_lt` and the periodic-point
     API, but no declaration combining arbitrary finite self-maps, eventual periodicity, and
     exclusion of period one from a fixed-point-free hypothesis.
   * The imported repository theorem already packages the exact Mathlib pigeonhole argument;
     this module adds only the fixed-point-free lower bound on the resulting period. -/

namespace D5.S3.ObserverMemory.Dynamics.FiniteNoFixedPointOrbit

open D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound

/-- Every orbit of a fixed-point-free self-map on a finite type reaches a cycle of period at
least two, with the tail and period fitting inside the carrier cardinality. -/
theorem finite_no_fixed_point_orbit_eventually_periodic
    {X : Type*} [Fintype X] (T : X -> X)
    (fixedPointFree : forall x, T x ≠ x) (initial : X) :
    exists mu period : Nat,
      mu + period <= Fintype.card X /\
        2 <= period /\
          forall t : Nat, mu <= t ->
            (T^[t + period]) initial = (T^[t]) initial := by
  obtain ⟨mu, period, period_pos, bound, tail_periodic⟩ :=
    finite_orbit_and_readout_eventually_periodic
      T (fun _ : X => Unit.unit) initial
  have period_ne_one : period ≠ 1 := by
    intro period_eq
    have orbit_eq := (tail_periodic mu (Nat.le_refl mu)).1
    subst period
    rw [show mu + 1 = mu.succ by omega, Function.iterate_succ_apply'] at orbit_eq
    exact fixedPointFree ((T^[mu]) initial) orbit_eq
  refine ⟨mu, period, bound, by omega, ?_⟩
  intro t ht
  exact (tail_periodic t ht).1

#print axioms finite_no_fixed_point_orbit_eventually_periodic

end D5.S3.ObserverMemory.Dynamics.FiniteNoFixedPointOrbit
