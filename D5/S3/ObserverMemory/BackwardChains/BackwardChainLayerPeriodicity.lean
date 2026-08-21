/- GID: D5/S3/ObserverMemory/BackwardChains/BackwardChainLayerPeriodicity
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/BackwardChains/BackwardChainLayerPeriodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Infinite backward chains and all predecessor layers characterize periodic points. -/

import D5.S3.ObserverMemory.BackwardChains.BackwardChainPeriodicity
import D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.BackwardChains.BackwardChainLayerPeriodicity

open D5.S3.ObserverMemory.BackwardChains.BackwardChainPeriodicity
open D5.S3.ObserverMemory.InverseLimits.BackwardOrbitCore
open D5.S3.ObserverMemory.InverseLimits.StableImagePeriodicCore

/- The layer is the source predecessor relation at an arbitrary iterate depth. -/
def PredecessorLayer {Y : Type*} (tau : Y -> Y) (y : Y) (k : Nat) : Set Y :=
  {x | (tau^[k]) x = y}

theorem backward_chain_and_layer_iff_periodic
    {Y : Type*} [Finite Y] (tau : Y -> Y) (y : Y) :
    (InfiniteBackwardChain tau y ↔ y ∈ Function.periodicPts tau) ∧
      ((∀ k : Nat, (PredecessorLayer tau y k).Nonempty) ↔
        y ∈ Function.periodicPts tau) := by
  constructor
  · exact infinite_backward_chain_iff_periodic tau y
  · constructor
    · intro h
      letI := Fintype.ofFinite Y
      have hyRange : y ∈ Set.range (tau^[Fintype.card Y]) := by
        rcases h (Fintype.card Y) with ⟨x, hx⟩
        change (tau^[Fintype.card Y]) x = y at hx
        exact ⟨x, hx⟩
      have hstable :
          Set.range (tau^[Fintype.card Y]) = Function.periodicPts tau :=
        (iterate_range_card_antitone_and_stable tau).2 _ le_rfl
      rw [hstable] at hyRange
      exact hyRange
    · intro hy k
      rcases (infinite_backward_chain_iff_periodic tau y).2 hy with ⟨orbit, hzero⟩
      refine ⟨orbit.1 k, ?_⟩
      change (tau^[k]) (orbit.1 k) = y
      have hstep := backward_iterate_apply orbit 0 k
      simpa [hzero] using hstep

#print axioms backward_chain_and_layer_iff_periodic

end D5.S3.ObserverMemory.BackwardChains.BackwardChainLayerPeriodicity
