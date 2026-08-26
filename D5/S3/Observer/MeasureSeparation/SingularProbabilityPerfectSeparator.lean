/- GID: D5/S3/Observer/MeasureSeparation/SingularProbabilityPerfectSeparator
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/SingularProbabilityPerfectSeparator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mutually singular probability laws admit a measurable perfect separator. -/

import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/- Library-search audit trail (2026-08-25):
   * Repository searches found no exact D5 theorem at this generality;
     `CountableSingularPartition` has additional countable-family and weight
     premises, while the existing Boolean transcript theorem is a special case.
   * Exact pinned-Mathlib hits `MutuallySingular.nullSet`,
     `measurableSet_nullSet`, `measure_nullSet`, and `measure_compl_nullSet`
     supply the canonical measurable singular-set witness and both null clauses.
   * Pinned Mathlib's `measure_compl` and the probability-measure instance turn
     the first null clause into full mass for the complementary event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped MeasureTheory

namespace D5.S3.Observer.MeasureSeparation.SingularProbabilityPerfectSeparator

/-- Mutually singular probability laws on a transcript space admit a measurable
event of probability one under the first law and zero under the second. -/
theorem mutually_singular_probability_laws_have_perfect_separator
    {Transcript : Type*} [MeasurableSpace Transcript]
    (probabilityX probabilityY : Measure Transcript)
    [IsProbabilityMeasure probabilityX]
    [IsProbabilityMeasure probabilityY]
    (singular : probabilityX ⟂ₘ probabilityY) :
    ∃ event : Set Transcript,
      MeasurableSet event ∧
        probabilityX event = 1 ∧ probabilityY event = 0 := by
  refine ⟨singular.nullSetᶜ, singular.measurableSet_nullSet.compl, ?_,
    singular.measure_compl_nullSet⟩
  rw [measure_compl singular.measurableSet_nullSet (by simp),
    singular.measure_nullSet, measure_univ, tsub_zero]

#print axioms mutually_singular_probability_laws_have_perfect_separator

end D5.S3.Observer.MeasureSeparation.SingularProbabilityPerfectSeparator
