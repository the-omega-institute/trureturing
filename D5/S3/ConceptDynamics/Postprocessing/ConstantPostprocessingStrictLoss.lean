/- GID: D5/S3/ConceptDynamics/Postprocessing/ConstantPostprocessingStrictLoss
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Postprocessing/ConstantPostprocessingStrictLoss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Constant postprocessing strictly loses every witnessed distinction. -/

import D5.S3.ConceptDynamics.Postprocessing.PostprocessingKernelMonotonicity

/- Library-search audit trail (2026-08-29):
   * The imported monotonicity theorem gives the non-strict inclusion for every
     postprocessing map.
   * Repository searches found no general theorem upgrading that inclusion to
     strictness from an explicit pair distinguished by the original readout.
   * The constant output witnesses collapse of that pair, while the supplied
     inequality witnesses that it was absent from the original kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Postprocessing.ConstantPostprocessingStrictLoss

open D5.S3.ConceptDynamics.Postprocessing.PostprocessingKernelMonotonicity

universe u v w

/-- Constant postprocessing strictly enlarges the equality kernel whenever the
original readout distinguishes at least one pair. -/
theorem constant_postprocessing_strictly_enlarges_kernel
    {X : Type u} {Y : Type v} {Z : Type w}
    (readout : X -> Y) (collapsed : Z)
    (x y : X) (separated : readout x ≠ readout y) :
    Setoid.ker readout <
      Setoid.ker ((fun _ : Y => collapsed) ∘ readout) := by
  constructor
  · exact postprocessing_kernel_mono readout (fun _ : Y => collapsed)
  · intro reverseInclusion
    have collapsedPair :
        Setoid.ker ((fun _ : Y => collapsed) ∘ readout) x y := by
      rfl
    exact separated (reverseInclusion collapsedPair)

/-- Satisfiability probe: a constant kernel strictly contains the Boolean
identity kernel. -/
example :
    Setoid.ker (fun x : Bool => x) <
      Setoid.ker (fun _ : Bool => PUnit.unit) := by
  constructor
  · intro x y same
    rfl
  · intro reverseInclusion
    exact Bool.false_ne_true (reverseInclusion rfl)

#print axioms constant_postprocessing_strictly_enlarges_kernel

end D5.S3.ConceptDynamics.Postprocessing.ConstantPostprocessingStrictLoss
