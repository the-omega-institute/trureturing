/- GID: D5/S3/ConceptDynamics/ObservationOrder/PostprocessingKernelMonotonicity
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/ObservationOrder/PostprocessingKernelMonotonicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Postprocessing can only enlarge a readout equality kernel. -/

import Mathlib.Data.Setoid.Basic

/- Library-search audit trail (2026-08-29):
   * D5 searches found target-relative refinement and finite indexed-readout
     monotonicity, but no standalone theorem for arbitrary function
     postprocessing at this generality.
   * The adjacent indexed-readout module records that pinned Mathlib has no
     exact `Setoid.ker` composition-inclusion theorem.
   * The proof uses equality congruence under the postprocessing map directly;
     no effectiveness, inhabitedness, finiteness, or decidable equality is
     required.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.ObservationOrder.PostprocessingKernelMonotonicity

universe u v w

/-- Equal source readouts remain equal after every deterministic
postprocessing, so postprocessing cannot shrink the equality kernel. -/
theorem postprocessing_kernel_mono
    {X : Type u} {Y : Type v} {Z : Type w}
    (readout : X -> Y) (postprocess : Y -> Z) :
    Setoid.ker readout <= Setoid.ker (postprocess ∘ readout) := by
  intro x y sameReadout
  exact congrArg postprocess sameReadout

/-- Strictness probe: constant postprocessing can identify two states that an
identity readout separates. -/
example :
    Setoid.ker (fun x : Bool => x) <
      Setoid.ker ((fun _ : Bool => PUnit.unit) ∘ fun x : Bool => x) := by
  constructor
  · exact postprocessing_kernel_mono (fun x : Bool => x)
      (fun _ : Bool => PUnit.unit)
  · intro reverse
    have collapsed :
        Setoid.ker ((fun _ : Bool => PUnit.unit) ∘ fun x : Bool => x)
          false true := by
      rfl
    exact Bool.false_ne_true (reverse collapsed)

#print axioms postprocessing_kernel_mono

end D5.S3.ConceptDynamics.ObservationOrder.PostprocessingKernelMonotonicity
