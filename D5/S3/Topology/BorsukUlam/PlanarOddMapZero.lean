/- GID: D5/S3/Topology/BorsukUlam/PlanarOddMapZero
   generality: G
   mirror-B: D5/B/S3/Topology/BorsukUlam/PlanarOddMapZero
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Every continuous odd map from the two-sphere to the plane has a zero. -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.IsometricSMul

/-! The planar Borsuk--Ulam route used by the chiral-event settlement. -/

set_option autoImplicit false

open scoped EuclideanSpace

namespace D5.S3.Topology.BorsukUlam.PlanarOddMapZero

def unitSphere : Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The planar Borsuk--Ulam theorem in the form used by the chiral-event argument. -/
theorem planar_odd_map_zero (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hf : ContinuousOn f unitSphere)
    (hodd : ∀ v ∈ unitSphere, f (-v) = -f v) :
    ∃ v ∈ unitSphere, f v = 0 := by
  sorry

end D5.S3.Topology.BorsukUlam.PlanarOddMapZero
