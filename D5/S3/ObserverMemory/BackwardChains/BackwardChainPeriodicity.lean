/- GID: D5/S3/ObserverMemory/BackwardChains/BackwardChainPeriodicity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/BackwardChains/BackwardChainPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An infinite compatible backward chain exists exactly at a periodic point. -/

import D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.BackwardChains.BackwardChainPeriodicity

open D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore

/- The chain is the source's infinite compatible predecessor family, based at y. -/
def InfiniteBackwardChain {Y : Type*} (tau : Y -> Y) (y : Y) : Prop :=
  ∃ orbit : BackwardOrbit tau, orbit.1 0 = y

theorem infinite_backward_chain_iff_periodic
    {Y : Type*} [Finite Y] (tau : Y -> Y) (y : Y) :
    InfiniteBackwardChain tau y ↔ y ∈ Function.periodicPts tau := by
  constructor
  · rintro ⟨orbit, hzero⟩
    rw [← hzero]
    exact backward_orbit_coordinate_periodic orbit 0
  · intro hy
    have hbij := backward_orbit_eval_zero_bijective tau
    rcases hbij.2 (⟨y, hy⟩ : {point : Y // point ∈ Function.periodicPts tau}) with
      ⟨orbit, hEq⟩
    refine ⟨orbit, ?_⟩
    exact congrArg Subtype.val hEq

#print axioms infinite_backward_chain_iff_periodic

end D5.S3.ObserverMemory.BackwardChains.BackwardChainPeriodicity
