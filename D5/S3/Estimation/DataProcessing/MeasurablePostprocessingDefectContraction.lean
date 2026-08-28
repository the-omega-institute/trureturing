/- GID: D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Measurable target postprocessing contracts the fiberwise kernel defect. -/

import Mathlib.Probability.Kernel.Composition.MapComap

/- Library-search audit trail (2026-08-27):
   * The finite D5 theorem `postprocessed_descent_defect_le` is not an exact hit:
     it assumes finite discrete carriers and models postprocessing by a zero-one
     stochastic matrix, while the source quantifies measurable maps and kernels.
   * Repository searches for event-supremum measure distance and nested
     `Kernel.map` defect constructions found no existing D5 primitive by either
     name or body shape.
   * Pinned Mathlib supplies the exact `Kernel.map`, `Kernel.map_apply`, and
     `Measure.map_apply` primitives. It has signed/vector-measure variation but
     no probability-measure total-variation distance or contraction theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

open MeasureTheory ProbabilityTheory

/-- The total-variation distance of two measures, expressed as the supremum of
their two directed gaps over measurable events. -/
noncomputable def measurableTotalVariation {A : Type*} [MeasurableSpace A]
    (mu nu : Measure A) : ENNReal :=
  ⨆ event : {event : Set A // MeasurableSet event},
    max (mu event.1 - nu event.1) (nu event.1 - mu event.1)

/-- The largest observable-law distance between states in one source readout
fiber. The observable law is constructed by mapping each kernel row through
the readout. -/
noncomputable def observableKernelDefect
    {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (K : Kernel X X) (q : X -> B) : ENNReal :=
  ⨆ pair : {pair : X × X // q pair.1 = q pair.2},
    measurableTotalVariation
      ((Kernel.map K q) pair.1.1) ((Kernel.map K q) pair.1.2)

/-- The same source-fiber defect after mapping each observable law through a
measurable target postprocessor. -/
noncomputable def postprocessedObservableKernelDefect
    {X B C : Type*} [MeasurableSpace X] [MeasurableSpace B]
    [MeasurableSpace C]
    (K : Kernel X X) (q : X -> B) (r : B -> C) : ENNReal :=
  ⨆ pair : {pair : X × X // q pair.1 = q pair.2},
    measurableTotalVariation
      ((Kernel.map (Kernel.map K q) r) pair.1.1)
      ((Kernel.map (Kernel.map K q) r) pair.1.2)

private theorem observable_kernel_pair_le
    {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    (K : Kernel X X) (q : X -> B)
    (pair : {pair : X × X // q pair.1 = q pair.2}) :
    measurableTotalVariation
        ((Kernel.map K q) pair.1.1) ((Kernel.map K q) pair.1.2) <=
      observableKernelDefect K q := by
  unfold observableKernelDefect
  exact le_iSup
    (fun candidate : {pair : X × X // q pair.1 = q pair.2} =>
      measurableTotalVariation
        ((Kernel.map K q) candidate.1.1)
        ((Kernel.map K q) candidate.1.2)) pair

private theorem measurable_total_variation_map_le
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    (mu nu : Measure B) (r : B -> C) (hr : Measurable r) :
    measurableTotalVariation (mu.map r) (nu.map r) <=
      measurableTotalVariation mu nu := by
  unfold measurableTotalVariation
  refine iSup_le fun event => ?_
  refine le_iSup_of_le
    (⟨r ⁻¹' event.1, hr event.2⟩ : {event : Set B // MeasurableSet event}) ?_
  rw [Measure.map_apply hr event.2, Measure.map_apply hr event.2]

/-- Measurable target postprocessing cannot increase the fixed-source-fiber
defect of the observable laws of a kernel. -/
theorem measurable_postprocessing_defect_le
    {X B C : Type*} [MeasurableSpace X] [MeasurableSpace B]
    [MeasurableSpace C]
    (K : Kernel X X) (q : X -> B) (r : B -> C) (hr : Measurable r) :
    postprocessedObservableKernelDefect K q r <= observableKernelDefect K q := by
  unfold postprocessedObservableKernelDefect
  refine iSup_le fun pair => ?_
  calc
    measurableTotalVariation
        ((Kernel.map (Kernel.map K q) r) pair.1.1)
        ((Kernel.map (Kernel.map K q) r) pair.1.2) =
        measurableTotalVariation
          (((Kernel.map K q) pair.1.1).map r)
          (((Kernel.map K q) pair.1.2).map r) := by
      rw [Kernel.map_apply _ hr, Kernel.map_apply _ hr]
    _ <= measurableTotalVariation
        ((Kernel.map K q) pair.1.1) ((Kernel.map K q) pair.1.2) :=
      measurable_total_variation_map_le _ _ r hr
    _ <= observableKernelDefect K q := observable_kernel_pair_le K q pair

#print axioms measurable_postprocessing_defect_le

end D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
