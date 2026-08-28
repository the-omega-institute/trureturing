/- GID: D5/S3/Observer/MeasureSeparation/EquivalentLawPosteriorInterior
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/EquivalentLawPosteriorInterior
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equivalent laws keep posterior limits interior and rule out perfect separation. -/

import D5.S3.Observer.MeasureSeparation.EquivalentMeasuresExcludePerfectSeparator
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/- Library-search audit trail (2026-08-25):
   * Repository searches for equivalent transcript laws, mixed laws,
     Radon--Nikodym posteriors, and zero-error separators found the adjacent
     `equivalent_probability_laws_exclude_perfect_separator`, which supplies
     only the second public clause and is applied directly below.
   * Pinned Mathlib supplies the exact primitives `Measure.rnDeriv_pos`,
     `Measure.rnDeriv_lt_top`, `Measure.smul_absolutelyContinuous`, and
     `Measure.AbsolutelyContinuous.ae_le`; no pinned theorem packages the two
     public clauses with a nondegenerate prior.
   * Body-shape searches for posterior and mixture definitions found only
     unrelated finite-state primitives. This module introduces no definition:
     both the likelihood posterior and its prior mixture law are constructed
     inline from the source measures and prior.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal MeasureTheory
open D5.S3.Observer.MeasureSeparation.EquivalentMeasuresExcludePerfectSeparator

namespace D5.S3.Observer.MeasureSeparation.EquivalentLawPosteriorInterior

/-- Under mutually absolutely continuous transcript laws and a nondegenerate
binary prior, the Radon--Nikodym limiting posterior lies strictly between zero
and one almost everywhere under the prior mixture. The same equivalence also
rules out a measurable zero-error separator. -/
theorem equivalent_law_posterior_stays_interior
    {Transcript : Type*} [MeasurableSpace Transcript]
    (probabilityX probabilityY : Measure Transcript)
    [IsProbabilityMeasure probabilityX]
    [IsProbabilityMeasure probabilityY]
    (prior : Real)
    (prior_pos : 0 < prior)
    (prior_lt_one : prior < 1)
    (equivalent : probabilityX ≪ probabilityY ∧ probabilityY ≪ probabilityX) :
    (∀ᵐ transcript ∂
        ENNReal.ofReal prior • probabilityX +
          ENNReal.ofReal (1 - prior) • probabilityY,
      0 <
          prior * (probabilityX.rnDeriv probabilityY transcript).toReal /
            (prior * (probabilityX.rnDeriv probabilityY transcript).toReal +
              (1 - prior)) ∧
        prior * (probabilityX.rnDeriv probabilityY transcript).toReal /
            (prior * (probabilityX.rnDeriv probabilityY transcript).toReal +
              (1 - prior)) < 1) ∧
      ¬ ∃ event : Set Transcript,
        MeasurableSet event ∧
          probabilityX event = 1 ∧ probabilityY event = 0 := by
  constructor
  · have mixed_absolutely_continuous :
        ENNReal.ofReal prior • probabilityX +
            ENNReal.ofReal (1 - prior) • probabilityY ≪ probabilityY :=
      Measure.AbsolutelyContinuous.add_left
        (Measure.smul_absolutelyContinuous.trans equivalent.1)
        Measure.smul_absolutelyContinuous
    have likelihood_pos :
        ∀ᵐ transcript ∂probabilityY,
          0 < probabilityX.rnDeriv probabilityY transcript :=
      equivalent.2.ae_le (Measure.rnDeriv_pos equivalent.1)
    filter_upwards
      [mixed_absolutely_continuous.ae_le likelihood_pos,
        mixed_absolutely_continuous.ae_le
          (Measure.rnDeriv_lt_top probabilityX probabilityY)]
      with transcript likelihood_positive likelihood_finite
    have likelihood_toReal_pos :
        0 < (probabilityX.rnDeriv probabilityY transcript).toReal :=
      ENNReal.toReal_pos likelihood_positive.ne' likelihood_finite.ne
    have complement_pos : 0 < 1 - prior := sub_pos.mpr prior_lt_one
    have denominator_pos :
        0 < prior * (probabilityX.rnDeriv probabilityY transcript).toReal +
          (1 - prior) :=
      add_pos_of_pos_of_nonneg
        (mul_pos prior_pos likelihood_toReal_pos) complement_pos.le
    constructor
    · exact div_pos (mul_pos prior_pos likelihood_toReal_pos) denominator_pos
    · exact (div_lt_one denominator_pos).2
        (lt_add_of_pos_right _ complement_pos)
  · exact equivalent_probability_laws_exclude_perfect_separator
      probabilityX probabilityY equivalent

example : Unit := ()

example : (0 : Real) < (1 / 2 : Real) ∧ (1 / 2 : Real) < 1 := by
  norm_num

example :
    (Measure.dirac () : Measure Unit) ≪ Measure.dirac () ∧
      (Measure.dirac () : Measure Unit) ≪ Measure.dirac () := by
  exact ⟨Measure.AbsolutelyContinuous.rfl, Measure.AbsolutelyContinuous.rfl⟩

#print axioms equivalent_law_posterior_stays_interior

end D5.S3.Observer.MeasureSeparation.EquivalentLawPosteriorInterior
