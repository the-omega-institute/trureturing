/- GID: D5/S1/Solenoid/PathOrbitClassification
   generality: I
   mirror-B: D5/B/S1/Solenoid/PathOrbitClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Path-connected solenoid points are exactly points on one real-flow orbit. -/

/- Library-search audit trail (2026-08-13):
   * `Path`, `Path.mk`, and `Joined` were found in the pinned Mathlib topology API.
   * `ContinuousMap.IccExtendCM` was found as the canonical continuous extension of a
     unit-interval map to the real line.
   * No Mathlib theorem classifies universal-solenoid path components. The forward
     direction is a thin endpoint corollary of the local theorem
     `StreamlineDecomposition.existsUnique_normalized_streamline`.
-/

import D5.S1.Solenoid.StreamlineDecomposition
import Mathlib.Topology.ContinuousMap.Interval

namespace D5.S1.Solenoid.PathOrbitClassification

open D5.S1.Dynamics

/-- Two points of the universal solenoid are joined by a continuous path exactly
when their difference is a real-flow element. This formalizes only the orbit
classification clause; the quotient parametrization and uncountability claims
of the source corollary remain outside this partial closure. -/
theorem path_joined_iff_real_flow_orbit (x y : UniversalSolenoid) :
    Joined x y ↔ ∃ t : Real, y = UniversalSolenoid.realFlow t + x := by
  constructor
  · rintro ⟨path⟩
    let extendedPath : C(Real, UniversalSolenoid) :=
      ContinuousMap.IccExtendCM path.toContinuousMap
    rcases StreamlineDecomposition.existsUnique_normalized_streamline
        extendedPath 0 with ⟨data, hdata, _⟩
    refine ⟨data.1 1 - data.1 0, ?_⟩
    have hzero : extendedPath 0 = x := by
      simp [extendedPath, path.source]
    have hone : extendedPath 1 = y := by
      simp [extendedPath, path.target]
    rw [← hzero, ← hone, hdata.2 0, hdata.2 1]
    calc
      UniversalSolenoid.realFlow (data.1 1) + data.2.1 =
          UniversalSolenoid.realFlow
            ((data.1 1 - data.1 0) + data.1 0) + data.2.1 := by
              rw [sub_add_cancel]
      _ = (UniversalSolenoid.realFlow (data.1 1 - data.1 0) +
            UniversalSolenoid.realFlow (data.1 0)) + data.2.1 := by
              rw [UniversalSolenoid.realFlow_add]
      _ = UniversalSolenoid.realFlow (data.1 1 - data.1 0) +
            (UniversalSolenoid.realFlow (data.1 0) + data.2.1) := by
              abel
  · rintro ⟨t, rfl⟩
    refine ⟨Path.mk
      ⟨fun u => UniversalSolenoid.realFlow ((u : Real) * t) + x,
        (UniversalSolenoid.continuous_realFlow.comp
          (continuous_subtype_val.mul continuous_const)).add continuous_const⟩ ?_ ?_⟩
    · simp [UniversalSolenoid.realFlow_zero]
    · simp

/-- Anti-vacuity witness: the zero point and the time-one real-flow point are
joined and distinct. -/
theorem zero_joined_realFlow_one_nontrivially :
    Joined (0 : UniversalSolenoid) (UniversalSolenoid.realFlow 1) ∧
      UniversalSolenoid.realFlow 1 ≠ 0 := by
  constructor
  · exact (path_joined_iff_real_flow_orbit 0 (UniversalSolenoid.realFlow 1)).2
      ⟨1, by simp⟩
  · simpa [StreamlineDecomposition.hiddenUnitOffset] using
      StreamlineDecomposition.hiddenUnitOffset_ne_zero

end D5.S1.Solenoid.PathOrbitClassification
