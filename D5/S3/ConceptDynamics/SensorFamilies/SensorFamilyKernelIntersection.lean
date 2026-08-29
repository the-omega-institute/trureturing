/- GID: D5/S3/ConceptDynamics/ObservationOrder/SensorFamilyKernelIntersection
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/SensorFamilyKernelIntersection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A joint sensor kernel is the intersection of all coordinate kernels. -/

import Mathlib.Data.Setoid.Basic
import Mathlib.Data.Set.Lattice

/- Library-search audit trail (2026-08-29):
   * D5 searches found finite-quotient and trajectory-specific intersection
     identities, but no theorem for an arbitrary indexed family of ordinary
     readout functions.
   * Pinned Mathlib supplies `Setoid.ker`, `Set.mem_iInter`, and function
     extensionality. Equality of joint readouts is equivalent to coordinatewise
     equality for every sensor.
   * The index type may be finite, infinite, or empty.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationOrder.SensorFamilyKernelIntersection

universe u v w

/-- The equality kernel of the function-valued joint readout is exactly the
intersection of the equality kernels of all sensor coordinates. -/
theorem joint_readout_kernel_eq_iInter
    {Index : Type u} {X : Type v} {O : Type w}
    (sensor : Index -> X -> O) :
    {pair : X × X |
      Setoid.ker (fun x i => sensor i x) pair.1 pair.2} =
      ⋂ index : Index,
        {pair : X × X | Setoid.ker (sensor index) pair.1 pair.2} := by
  ext pair
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Setoid.ker_def]
  constructor
  · intro sameJoint index
    exact congrFun sameJoint index
  · intro sameCoordinates
    funext index
    exact sameCoordinates index

/-- Satisfiability probe: a one-coordinate Boolean identity family has the
expected intersection description. -/
example :
    {pair : Bool × Bool |
      Setoid.ker (fun x : Bool => fun _ : PUnit => x) pair.1 pair.2} =
      ⋂ index : PUnit,
        {pair : Bool × Bool |
          Setoid.ker ((fun _ : PUnit => fun x : Bool => x) index)
            pair.1 pair.2} := by
  exact joint_readout_kernel_eq_iInter
    (fun _ : PUnit => fun x : Bool => x)

#print axioms joint_readout_kernel_eq_iInter

end D5.S3.ConceptDynamics.ObservationOrder.SensorFamilyKernelIntersection
