/- GID: D5/S3/ConceptDynamics/ObservationOrder/InjectivePostprocessingKernelEquality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/InjectivePostprocessingKernelEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Injective postprocessing preserves an observation kernel exactly. -/

import Mathlib.Logic.Function.Basic

/- Library-search audit trail (2026-08-29):
   * The statement is formulated over arbitrary types and functions.
   * Pinned Mathlib supplies only the elementary logical and function facts
     used below.
   * No finiteness, decidable equality, topology, probability, or algebraic
     structure is assumed unless it occurs explicitly in the theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationOrder.InjectivePostprocessingKernelEquality

universe u v w

def Kernel {State : Type u} {Output : Type v}
    (readout : State -> Output) (x y : State) : Prop :=
  readout x = readout y

/-- Injective postprocessing neither creates nor removes readout collisions. -/
theorem injective_postprocessing_preserves_kernel
    {State : Type u} {Output : Type v} {Processed : Type w}
    (readout : State -> Output) (postprocess : Output -> Processed)
    (postprocessInjective : Function.Injective postprocess)
    (x y : State) :
    Kernel (postprocess ∘ readout) x y ↔ Kernel readout x y := by
  constructor
  · intro sameProcessed
    exact postprocessInjective sameProcessed
  · intro sameReadout
    exact congrArg postprocess sameReadout

#print axioms injective_postprocessing_preserves_kernel

end D5.S3.ConceptDynamics.ObservationOrder.InjectivePostprocessingKernelEquality
