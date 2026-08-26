/- GID: D5/S1/Solenoid/Connectivity/SameFiberPathOrbitCriterion
   generality: I
   mirror-B: D5/B/S1/Solenoid/Connectivity/SameFiberPathOrbitCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Same-projection solenoid points are path joined exactly at integer real-flow times. -/

import D5.S1.Solenoid.PathOrbitClassification

/- Library-search audit trail (2026-08-26):
   * Exact repository hit `path_joined_iff_real_flow_orbit` classifies joined
     solenoid points by arbitrary real-flow time and is applied in both directions.
   * Its public signature lacks the same-projection premise and the consequent
     integer-time restriction, so it is not an exact whole-statement bind.
   * Exact pinned-Mathlib hit `AddCircle.coe_eq_zero_iff` says that a real number
     vanishes modulo period one exactly when it is an integer multiple of one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Solenoid.Connectivity.SameFiberPathOrbitCriterion

open D5.S1.Dynamics
open D5.S1.Solenoid.PathOrbitClassification

/-- Within one visible projection fiber, path connectedness is exactly
translation by the integer-time subgroup of the real flow. -/
theorem same_fiber_path_orbit_criterion (x y : UniversalSolenoid)
    (sameProjection : UniversalSolenoid.projection x =
      UniversalSolenoid.projection y) :
    Joined x y ↔
      ∃ n : Int, y = UniversalSolenoid.realFlow (n : Real) + x := by
  constructor
  · intro joined
    rcases (path_joined_iff_real_flow_orbit x y).1 joined with ⟨t, ht⟩
    have projectionEquality :
        UniversalSolenoid.projection x =
          (t : AddCircle (1 : Real)) + UniversalSolenoid.projection x := by
      calc
        UniversalSolenoid.projection x =
            UniversalSolenoid.projection y := sameProjection
        _ = UniversalSolenoid.projection
            (UniversalSolenoid.realFlow t + x) := congrArg _ ht
        _ = UniversalSolenoid.projection (UniversalSolenoid.realFlow t) +
            UniversalSolenoid.projection x := by
          rw [map_add]
        _ = (t : AddCircle (1 : Real)) +
            UniversalSolenoid.projection x := by
          rw [UniversalSolenoid.projection_realFlow]
    have timeVanishes : (t : AddCircle (1 : Real)) = 0 := by
      apply add_right_cancel (b := UniversalSolenoid.projection x)
      simpa using projectionEquality.symm
    rcases (AddCircle.coe_eq_zero_iff (1 : Real)).1 timeVanishes with
      ⟨n, hn⟩
    have integerTime : (n : Real) = t := by
      simpa using hn
    refine ⟨n, ?_⟩
    calc
      y = UniversalSolenoid.realFlow t + x := ht
      _ = UniversalSolenoid.realFlow (n : Real) + x :=
        congrArg (fun time => UniversalSolenoid.realFlow time + x)
          integerTime.symm
  · rintro ⟨n, rfl⟩
    exact (path_joined_iff_real_flow_orbit x
      (UniversalSolenoid.realFlow (n : Real) + x)).2 ⟨n, rfl⟩

#print axioms same_fiber_path_orbit_criterion

end D5.S1.Solenoid.Connectivity.SameFiberPathOrbitCriterion
