/- GID: D5/S3/ConceptDynamics/DefinitionEscapeMonotonicity/ChartLayerKernelStability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeMonotonicity/ChartLayerKernelStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Image-injective chart postprocessing preserves escape data and dimension. -/

import D5.S3.ObserverMemory.Refinement.PostprocessingKernelCalculus

/- Library-search audit trail (2026-09-01):
   * The target atom is residual-open with no formalization receipt. Its three
     same-section neighbors are also residual-open, and repository searches for
     chart layers, escape dimensions, kernel composition, and image injectivity
     found no declaration packaging all three requested conclusions.
   * Exact repository hit
     `postprocessing_kernel_eq_iff_injOn_range` proves the first conclusion with
     precisely `Set.InjOn postprocess (Set.range currentReadout)`. It is imported
     and applied directly rather than reproved. The nearby quotient, congruence,
     and subfamily-refinement theorems have different conclusions.
   * Pinned Mathlib provides `Setoid.ker`, `Setoid.ker_def`, `Set.InjOn`, and
     `Set.range`, but no equality-kernel theorem for postcomposition injective on
     the realized range. Searches of the other pinned Lean packages found no hit.
   * The source does not define `d_esc` in this atom. `escapeLayer` therefore
     abstracts data determined by the equality kernel, and `escapeDimension`
     abstracts its ordered numerical readout. No new definition or monotonicity
     hypothesis is introduced: equality already implies nonincrease. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.ChartLayerKernelStability

open D5.S3.ObserverMemory.Refinement.PostprocessingKernelCalculus

universe uState uCurrent uNext uEscape uDimension

/-- A chart layer obtained by postprocessing the current readout with a map
injective on realized values has the same equality kernel. Hence every escape
layer determined by that kernel is unchanged, and any ordered dimension of the
escape layer cannot increase. -/
theorem chart_layer_preserves_escape_dimension
    {State : Type uState} {Current : Type uCurrent} {Next : Type uNext}
    {Escape : Type uEscape} {Dimension : Type uDimension} [Preorder Dimension]
    (currentReadout : State -> Current) (nextReadout : State -> Next)
    (postprocess : Current -> Next) (escapeLayer : Setoid State -> Escape)
    (escapeDimension : Escape -> Dimension)
    (nextFactors : nextReadout = postprocess ∘ currentReadout)
    (injectiveOnImage : Set.InjOn postprocess (Set.range currentReadout)) :
    Setoid.ker nextReadout = Setoid.ker currentReadout /\
      escapeLayer (Setoid.ker nextReadout) =
        escapeLayer (Setoid.ker currentReadout) /\
      escapeDimension (escapeLayer (Setoid.ker nextReadout)) <=
        escapeDimension (escapeLayer (Setoid.ker currentReadout)) := by
  have kernelEquality : Setoid.ker nextReadout = Setoid.ker currentReadout := by
    rw [nextFactors]
    exact
      (postprocessing_kernel_eq_iff_injOn_range currentReadout postprocess).2
        injectiveOnImage
  have escapeEquality :
      escapeLayer (Setoid.ker nextReadout) =
        escapeLayer (Setoid.ker currentReadout) :=
    congrArg escapeLayer kernelEquality
  exact ⟨kernelEquality, escapeEquality, le_of_eq (congrArg escapeDimension escapeEquality)⟩

#print axioms chart_layer_preserves_escape_dimension

end D5.S3.ConceptDynamics.DefinitionEscapeMonotonicity.ChartLayerKernelStability
