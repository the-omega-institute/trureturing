/- GID: D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle
   generality: I
   mirror-B: D5/B/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The measurable total variation distance satisfies the triangle inequality. -/

import D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/- Library-search audit trail (2026-09-03):
   * Repository: no public form of this statement exists. Two frozen modules
     carry a `private` copy each, in `Estimation/DataProcessing/
     MeasurableDescentErrorBounds` and in `Estimation/SequentialDecisionRisk/
     MeasurableDeficiencyTriangle`. The repository does publicly name a
     triangle law for the finite total variation of real vectors,
     `D5/S3/TotalVariation/Metric.total_variation_triangle`, which is a
     different object: functions on a `Fintype` rather than measures.
   * Pinned Mathlib was searched by name and by concept for a triangle
     inequality on a supremum-over-events variation distance. The relatives
     found are the `Measure` lattice order lemmas and `tsub_le_tsub_add_tsub`,
     the truncated-subtraction step this proof uses. This search found no
     upstream statement for this repository's `measurableTotalVariation`, which
     is what the search shows and no more.
   * No new primitive is introduced. `measurableTotalVariation` is the frozen
     definition of `MeasurablePostprocessingDefectContraction`, used through the
     import above. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle

open MeasureTheory ProbabilityTheory
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction

/-- The triangle inequality for the supremum, over any index, of the larger of
two truncated differences.  Nothing about measures enters: the three families
are arbitrary `ENNReal`-valued functions, and the argument is the order theory of
truncated subtraction. -/
theorem iSup_max_tsub_triangle {Index : Type*} (f g h : Index -> ENNReal) :
    (⨆ i, max (f i - h i) (h i - f i)) <=
      (⨆ i, max (f i - g i) (g i - f i)) + ⨆ i, max (g i - h i) (h i - g i) := by
  refine iSup_le fun i => ?_
  have hfg : max (f i - g i) (g i - f i) <= ⨆ j, max (f j - g j) (g j - f j) :=
    le_iSup (fun j => max (f j - g j) (g j - f j)) i
  have hgh : max (g i - h i) (h i - g i) <= ⨆ j, max (g j - h j) (h j - g j) :=
    le_iSup (fun j => max (g j - h j) (h j - g j)) i
  apply max_le
  · calc
      f i - h i <= (f i - g i) + (g i - h i) := tsub_le_tsub_add_tsub
      _ <= _ := add_le_add
        (le_max_left _ _ |>.trans hfg) (le_max_left _ _ |>.trans hgh)
  · calc
      h i - f i <= (h i - g i) + (g i - f i) := tsub_le_tsub_add_tsub
      _ <= (⨆ j, max (g j - h j) (h j - g j)) + ⨆ j, max (f j - g j) (g j - f j) :=
        add_le_add (le_max_right _ _ |>.trans hgh) (le_max_right _ _ |>.trans hfg)
      _ = _ := add_comm _ _

/-- The measurable total variation distance satisfies the triangle inequality,
for arbitrary measures on a measurable space: no finiteness, no probability
normalisation, and no relation between the three measures is assumed.  It is the
event-indexed instance of the theorem above. -/
theorem measurable_total_variation_triangle
    {A : Type*} [MeasurableSpace A] (mu nu rho : Measure A) :
    measurableTotalVariation mu rho <=
      measurableTotalVariation mu nu + measurableTotalVariation nu rho := by
  unfold measurableTotalVariation
  exact iSup_max_tsub_triangle (fun event : {event : Set A // MeasurableSet event} => mu event.1)
    (fun event : {event : Set A // MeasurableSet event} => nu event.1)
    (fun event : {event : Set A // MeasurableSet event} => rho event.1)

/-- The measurable total variation distance is symmetric.  The repository
re-derives this twice: once as a private theorem in `MeasurableDescentErrorBounds`
and once inline, as the same `simp` call, inside a calculation in
`MeasurableDeficiencyTriangle`.  Counting declaration names alone would have
found only one of the two. -/
theorem measurable_total_variation_comm
    {A : Type*} [MeasurableSpace A] (mu nu : Measure A) :
    measurableTotalVariation mu nu = measurableTotalVariation nu mu := by
  simp only [measurableTotalVariation, max_comm]

end D5.S3.Estimation.DataProcessing.MeasurableTotalVariationTriangle
