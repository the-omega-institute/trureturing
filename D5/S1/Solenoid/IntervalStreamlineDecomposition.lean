/- GID: D5/S1/Solenoid/IntervalStreamlineDecomposition
   generality: I
   mirror-B: D5/B/S1/Solenoid/IntervalStreamlineDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every unit-interval solenoid path has one constant hidden offset. -/

/- Library-search audit trail (2026-08-16):
   * `ContinuousMap.IccExtendCM` and `ContinuousMap.IccExtendCM_of_mem` were
     exact pinned-Mathlib hits for extending a unit-interval path to the real line.
   * `StreamlineDecomposition.existsUnique_normalized_streamline` is the exact
     frozen repository theorem supplying the real lift and constant kernel offset.
   * No Mathlib theorem packages the universal-solenoid decomposition itself.
-/

import D5.S1.Solenoid.StreamlineDecomposition
import Mathlib.Topology.ContinuousMap.Interval

namespace D5.S1.Solenoid.IntervalStreamlineDecomposition

open Set
open D5.S1.Dynamics

/-- Every continuous path from the unit interval into the universal solenoid
has a continuous real lift and one time-independent compatible kernel element
that reconstruct the path at every time. -/
theorem exists_interval_streamline_decomposition
    (path : C(Set.Icc (0 : ℝ) 1, UniversalSolenoid)) :
    ∃ visibleLift : C(Set.Icc (0 : ℝ) 1, ℝ),
      ∃ hiddenOffset : UniversalSolenoid.projection.ker,
        ∀ t, path t =
          UniversalSolenoid.realFlow (visibleLift t) + hiddenOffset.1 := by
  let extendedPath : C(ℝ, UniversalSolenoid) :=
    ContinuousMap.IccExtendCM path
  rcases StreamlineDecomposition.existsUnique_normalized_streamline
      extendedPath 0 with ⟨data, hdata, _⟩
  let visibleLift : C(Set.Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t => data.1 t.1,
      data.1.continuous.comp continuous_subtype_val⟩
  refine ⟨visibleLift, data.2, fun t => ?_⟩
  simpa [extendedPath, visibleLift] using hdata.2 t.1

end D5.S1.Solenoid.IntervalStreamlineDecomposition
