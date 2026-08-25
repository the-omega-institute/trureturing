/- GID: D5/S3/Observer/MeasureSeparation/EquivalentMeasuresExcludePerfectSeparator
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/EquivalentMeasuresExcludePerfectSeparator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equivalent probability laws admit no measurable event separating them with zero error. -/

import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/- Library-search audit trail (2026-08-25):
   * Repository searches for equivalent probability laws, measurable separating
     events, and mass-one-versus-mass-zero events found no exact D5 theorem.
   * `CountableSingularPartition` is the adjacent opposite-regime result: it
     constructs disjoint full-measure supports for mutually singular laws.
   * Exact pinned-Mathlib hit `Measure.AbsolutelyContinuous` is the source's
     null-set transport primitive and is applied directly below.
   * No pinned-library theorem packages the public probability-measure,
     mutual-equivalence, measurability, and nonexistence clauses together.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped MeasureTheory

namespace D5.S3.Observer.MeasureSeparation.EquivalentMeasuresExcludePerfectSeparator

/-- Two mutually absolutely continuous probability laws on one transcript
space cannot assign masses one and zero to the same measurable event. -/
theorem equivalent_probability_laws_exclude_perfect_separator
    {Transcript : Type*} [MeasurableSpace Transcript]
    (probabilityX probabilityY : Measure Transcript)
    [IsProbabilityMeasure probabilityX]
    [IsProbabilityMeasure probabilityY]
    (equivalent : probabilityX ≪ probabilityY ∧ probabilityY ≪ probabilityX) :
    ¬ ∃ event : Set Transcript,
      MeasurableSet event ∧
        probabilityX event = 1 ∧ probabilityY event = 0 := by
  rintro ⟨event, _measurableEvent, fullUnderX, nullUnderY⟩
  have nullUnderX : probabilityX event = 0 := equivalent.1 nullUnderY
  exact one_ne_zero (fullUnderX.symm.trans nullUnderX)

#print axioms equivalent_probability_laws_exclude_perfect_separator

end D5.S3.Observer.MeasureSeparation.EquivalentMeasuresExcludePerfectSeparator
