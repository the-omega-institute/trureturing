/- GID: D5/S3/Observer/Refinement/CongruenceKernelSensorFusion
   generality: G
   mirror-B: D5/B/S3/Observer/Refinement/CongruenceKernelSensorFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Forward-congruence completion commutes with arbitrary sensor intersections. -/

import D5.S3.Observer.Separation.CongruenceKernel

/- Library-search audit trail (2026-08-29):
   * The exact completion operator `congruenceKernel` and its maximality laws
     are imported from the canonical observer-separation owner.
   * D5 searches for arbitrary intersections of `congruenceKernel` found no
     theorem identifying completion of a sensor intersection with the
     intersection of the completed sensors.
   * Pinned Mathlib supplies `Set.mem_iInter`; the proof is the direct exchange
     of the sensor and iterate universal quantifiers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Refinement.CongruenceKernelSensorFusion

open Set
open D5.S3.Observer.Separation.CongruenceKernel

universe u v

/-- The maximal forward-congruence interior of an arbitrary intersection is
exactly the intersection of the individual interiors. -/
theorem congruence_kernel_iInter
    {Index : Type u} {Y : Type v} (tau : Y -> Y)
    (relations : Index -> StateRelation Y) :
    congruenceKernel tau (⋂ index, relations index) =
      ⋂ index, congruenceKernel tau (relations index) := by
  ext pair
  simp only [congruenceKernel, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro allIterations index iteration
    exact allIterations iteration index
  · intro allSensors iteration index
    exact allSensors index iteration

/-- Inhabited-family probe: a one-sensor family is a valid instance of the
source hypotheses. -/
example {Y : Type v} (tau : Y -> Y) (relation : StateRelation Y) :
    congruenceKernel tau (⋂ _ : PUnit, relation) =
      ⋂ _ : PUnit, congruenceKernel tau relation :=
  congruence_kernel_iInter tau fun _ : PUnit => relation

#print axioms congruence_kernel_iInter

end D5.S3.Observer.Refinement.CongruenceKernelSensorFusion
