/- GID: D5/S3/ConceptDynamics/Postprocessing/PostprocessingStrictLossWitness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Postprocessing/PostprocessingStrictLossWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A collapsed distinction witnesses strict information loss under postprocessing. -/

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

namespace D5.S3.ConceptDynamics.Postprocessing.PostprocessingStrictLossWitness

universe u v w

def Kernel {State : Type u} {Output : Type v}
    (readout : State -> Output) (x y : State) : Prop :=
  readout x = readout y

/-- A pair separated before postprocessing and collapsed afterwards witnesses
strict enlargement of the observation kernel. -/
theorem collapsed_distinction_witnesses_strict_loss
    {State : Type u} {Output : Type v} {Processed : Type w}
    (readout : State -> Output) (postprocess : Output -> Processed)
    (x y : State)
    (separated : readout x ≠ readout y)
    (collapsed : postprocess (readout x) = postprocess (readout y)) :
    Kernel (postprocess ∘ readout) x y ∧ ¬ Kernel readout x y := by
  constructor
  · exact collapsed
  · exact separated

/-- Any strict-loss witness certifies failure of injectivity on the image of
the original readout. -/
theorem strict_loss_refutes_image_injectivity
    {State : Type u} {Output : Type v} {Processed : Type w}
    (readout : State -> Output) (postprocess : Output -> Processed)
    (x y : State)
    (separated : readout x ≠ readout y)
    (collapsed : postprocess (readout x) = postprocess (readout y)) :
    ¬ Function.Injective postprocess := by
  intro injective
  exact separated (injective collapsed)

#print axioms collapsed_distinction_witnesses_strict_loss
#print axioms strict_loss_refutes_image_injectivity

end D5.S3.ConceptDynamics.Postprocessing.PostprocessingStrictLossWitness
