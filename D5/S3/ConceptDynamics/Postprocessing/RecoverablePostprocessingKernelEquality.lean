/- GID: D5/S3/ConceptDynamics/Postprocessing/RecoverablePostprocessingKernelEquality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Postprocessing/RecoverablePostprocessingKernelEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recoverable postprocessing preserves the readout kernel exactly. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-29):
   * Repository searches for postprocessing, recovery, and equality kernels
     found specialized quotient and channel statements, but no arbitrary
     function-level theorem with recovery required only on the readout image.
   * Pinned Mathlib supplies `Setoid.ker`, composition, and equality congruence.
     Recovery reflects processed equality back to original equality.
   * Requiring recovery only at values produced by the readout is weaker than
     assuming the postprocessing map is globally injective.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Postprocessing.RecoverablePostprocessingKernelEquality

universe u v w

/-- If a recovery map reverses postprocessing on every value in the readout
image, then the original and processed equality kernels coincide. -/
theorem recoverable_postprocessing_preserves_kernel
    {X : Type u} {Y : Type v} {Z : Type w}
    (readout : X -> Y) (postprocess : Y -> Z) (recover : Z -> Y)
    (recovers : forall x : X, recover (postprocess (readout x)) = readout x) :
    Setoid.ker (postprocess ∘ readout) = Setoid.ker readout := by
  apply le_antisymm
  · intro x y sameProcessed
    have sameRecovered := congrArg recover sameProcessed
    simpa only [Setoid.ker_def, Function.comp_apply, recovers] using sameRecovered
  · intro x y sameReadout
    exact congrArg postprocess sameReadout

/-- Satisfiability probe: identity postprocessing is recoverable on every
Boolean readout value. -/
example :
    Setoid.ker ((fun x : Bool => x) ∘ (fun x : Bool => x)) =
      Setoid.ker (fun x : Bool => x) := by
  apply recoverable_postprocessing_preserves_kernel
      (readout := fun x : Bool => x)
      (postprocess := fun x : Bool => x)
      (recover := fun x : Bool => x)
  intro x
  rfl

#print axioms recoverable_postprocessing_preserves_kernel

end D5.S3.ConceptDynamics.Postprocessing.RecoverablePostprocessingKernelEquality
