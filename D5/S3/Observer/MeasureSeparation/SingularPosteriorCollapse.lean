/- GID: D5/S3/Observer/MeasureSeparation/SingularPosteriorCollapse
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/SingularPosteriorCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Singular-law posteriors collapse; degenerate priors and spaces are audited. -/

import D5.S3.Observer.MeasureSeparation.SingularProbabilityPerfectSeparator
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Distributions.Uniform

/- Library-search audit trail (2026-08-25):
   * Repository searches found the exact perfect-separator theorem but no
     posterior process or almost-sure convergence theorem built from it.
   * Pinned Mathlib type-shape searches for `Tendsto`, `forall eventually`,
     martingales, and conditional expectation found the exact theorem
     `MeasureTheory.Integrable.tendsto_ae_condExp` and the more general
     `MeasureTheory.Submartingale.ae_tendsto_limitProcess`.
   * The former is used: it identifies the limit as the separator indicator,
     while the latter only supplies an abstract limit process.
   * NyxID service discovery exposed no Loogle or LeanSearch endpoint. GitHub
     proxy searches for both theorem names returned HTTP 400 (`API key is
     failed`), so no external hit is claimed; the pinned source was inspected.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal MeasureTheory Topology

open D5.S3.Observer.MeasureSeparation.SingularProbabilityPerfectSeparator

namespace D5.S3.Observer.MeasureSeparation.SingularPosteriorCollapse

/-- The transcript law obtained by mixing the two state laws with a binary
prior. The `ofReal` totalization is harmless under the theorem's interior-prior
hypotheses and makes the definition available at both degenerate endpoints. -/
def binaryPriorMixture {Transcript : Type*} [MeasurableSpace Transcript]
    (prior : Real) (probabilityX probabilityY : Measure Transcript) :
    Measure Transcript :=
  ENNReal.ofReal prior • probabilityX +
    ENNReal.ofReal (1 - prior) • probabilityY

/-- The source section's likelihood form of the posterior probability of state
`x`. -/
def likelihoodPosterior (prior likelihood : Real) : Real :=
  prior * likelihood / (prior * likelihood + (1 - prior))

/-- The likelihood-form posterior evaluated along a likelihood-ratio process. -/
def likelihoodPosteriorProcess {Transcript : Type*} (prior : Real)
    (likelihood : Nat → Transcript → Real) : Nat → Transcript → Real :=
  fun time transcript ↦ likelihoodPosterior prior (likelihood time transcript)

/-- The posterior probability of the separating state event after observing
the information in `filtration time`. It is the conditional expectation of the
event indicator under the prior mixture law. -/
def binaryPosteriorProcess {Transcript : Type*} [MeasurableSpace Transcript]
    (mixture : Measure Transcript)
    (filtration : Filtration Nat ‹MeasurableSpace Transcript›)
    (event : Set Transcript) (time : Nat) (transcript : Transcript) : Real :=
  (mixture[event.indicator (fun _ ↦ (1 : Real)) | filtration time]) transcript

/-- For mutually singular state laws and an interior prior, the conditional
posterior of a perfect separating event converges almost surely to one under
the first law and to zero under the second law. -/
theorem mutually_singular_laws_have_collapsing_posterior
    {Transcript : Type*} [MeasurableSpace Transcript]
    (probabilityX probabilityY : Measure Transcript)
    [IsProbabilityMeasure probabilityX]
    [IsProbabilityMeasure probabilityY]
    (prior : Real) (prior_pos : 0 < prior) (prior_lt_one : prior < 1)
    (filtration : Filtration Nat ‹MeasurableSpace Transcript›)
    (generates : ⨆ time, filtration time = ‹MeasurableSpace Transcript›)
    (singular : probabilityX ⟂ₘ probabilityY) :
    ∃ event : Set Transcript,
      MeasurableSet event ∧
        probabilityX event = 1 ∧
          probabilityY event = 0 ∧
            (∀ᵐ transcript ∂probabilityX,
              Tendsto
                (fun time ↦ binaryPosteriorProcess
                  (binaryPriorMixture prior probabilityX probabilityY)
                  filtration event time transcript)
                atTop (𝓝 1)) ∧
              ∀ᵐ transcript ∂probabilityY,
                Tendsto
                  (fun time ↦ binaryPosteriorProcess
                    (binaryPriorMixture prior probabilityX probabilityY)
                    filtration event time transcript)
                  atTop (𝓝 0) := by
  obtain ⟨event, event_measurable, event_full_x, event_null_y⟩ :=
    mutually_singular_probability_laws_have_perfect_separator
      probabilityX probabilityY singular
  refine ⟨event, event_measurable, event_full_x, event_null_y, ?_⟩
  letI : IsFiniteMeasure
      (binaryPriorMixture prior probabilityX probabilityY) := by
    constructor
    simp [binaryPriorMixture, ENNReal.add_lt_top]
  have event_measurable_at_limit :
      MeasurableSet[⨆ time, filtration time] event := by
    rw [generates]
    exact event_measurable
  have indicator_integrable :
      Integrable (event.indicator (fun _ ↦ (1 : Real)))
        (binaryPriorMixture prior probabilityX probabilityY) :=
    (integrable_const (1 : Real)).indicator event_measurable
  have indicator_strongly_measurable :
      StronglyMeasurable[⨆ time, filtration time]
        (event.indicator (fun _ ↦ (1 : Real))) :=
    stronglyMeasurable_const.indicator event_measurable_at_limit
  have mixture_convergence :
      ∀ᵐ transcript ∂binaryPriorMixture prior probabilityX probabilityY,
        Tendsto
          (fun time ↦ binaryPosteriorProcess
            (binaryPriorMixture prior probabilityX probabilityY)
            filtration event time transcript)
          atTop (𝓝 (event.indicator (fun _ ↦ (1 : Real)) transcript)) := by
    simpa only [binaryPosteriorProcess] using
      indicator_integrable.tendsto_ae_condExp indicator_strongly_measurable
  have probability_x_ac :
      probabilityX ≪ binaryPriorMixture prior probabilityX probabilityY := by
    apply Measure.AbsolutelyContinuous.add_right
    exact Measure.AbsolutelyContinuous.rfl.smul_right
      (ENNReal.ofReal_ne_zero_iff.mpr prior_pos)
  have probability_y_ac :
      probabilityY ≪ binaryPriorMixture prior probabilityX probabilityY := by
    exact (Measure.AbsolutelyContinuous.rfl.smul_right
      (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr prior_lt_one))).add_right'
        (ENNReal.ofReal prior • probabilityX)
  constructor
  · filter_upwards
      [probability_x_ac.ae_le mixture_convergence,
        (mem_ae_iff_prob_eq_one event_measurable).2 event_full_x]
      with transcript convergence transcript_mem
    simpa [Set.indicator_of_mem transcript_mem] using convergence
  · filter_upwards
      [probability_y_ac.ae_le mixture_convergence,
        compl_mem_ae_iff.mpr event_null_y]
      with transcript convergence transcript_mem_compl
    have transcript_not_mem : transcript ∉ event := by
      simpa only [Set.mem_compl_iff] using transcript_mem_compl
    simpa [Set.indicator_of_notMem transcript_not_mem] using convergence

#print axioms mutually_singular_laws_have_collapsing_posterior

/-- At prior zero, even the constant unit likelihood gives a posterior process
that cannot converge to one. -/
theorem zero_prior_is_necessary :
    ¬ Tendsto
      (fun time : Nat ↦ likelihoodPosteriorProcess 0
        (fun (_ : Nat) (_ : Unit) ↦ (1 : Real)) time ())
      atTop (𝓝 1) := by
  simp [likelihoodPosteriorProcess, likelihoodPosterior]

#print axioms zero_prior_is_necessary

/-- At prior one, even the constant unit likelihood gives a posterior process
that cannot converge to zero. -/
theorem one_prior_is_necessary :
    ¬ Tendsto
      (fun time : Nat ↦ likelihoodPosteriorProcess 1
        (fun (_ : Nat) (_ : Unit) ↦ (1 : Real)) time ())
      atTop (𝓝 0) := by
  simp [likelihoodPosteriorProcess, likelihoodPosterior]

#print axioms one_prior_is_necessary

/-- Equal probability laws cannot supply the full-versus-null event needed for
posterior identification. -/
theorem equal_law_is_not_perfectly_separable :
    ¬ ∃ event : Set Unit,
      MeasurableSet event ∧
        (Measure.dirac () : Measure Unit) event = 1 ∧
          (Measure.dirac () : Measure Unit) event = 0 := by
  rintro ⟨event, _, event_full, event_null⟩
  rw [event_full] at event_null
  exact one_ne_zero event_null

#print axioms equal_law_is_not_perfectly_separable

/-- No probability law exists on an empty transcript type. Thus the theorem's
probability-law premises make the empty-space case vacuous. -/
theorem empty_transcript_has_no_probability_law :
    ¬ ∃ probability : Measure Empty, IsProbabilityMeasure probability := by
  rintro ⟨probability, probability_measure⟩
  letI : IsProbabilityMeasure probability := probability_measure
  rcases nonempty_of_isProbabilityMeasure probability with ⟨transcript⟩
  exact transcript.elim

#print axioms empty_transcript_has_no_probability_law

/-- All probability laws on the singleton transcript type coincide. -/
theorem unit_probability_laws_are_equal
    (probabilityX probabilityY : Measure Unit)
    [IsProbabilityMeasure probabilityX]
    [IsProbabilityMeasure probabilityY] :
    probabilityX = probabilityY := by
  ext event event_measurable
  by_cases unit_mem : () ∈ event
  · have event_eq_univ : event = Set.univ := by
      ext transcript
      simpa [Subsingleton.elim transcript ()] using unit_mem
    simp [event_eq_univ]
  · have event_eq_empty : event = ∅ := by
      ext transcript
      simpa [Subsingleton.elim transcript ()] using unit_mem
    simp [event_eq_empty]

#print axioms unit_probability_laws_are_equal

/-- The constant bottom filtration on a nontrivial Boolean transcript space
does not generate the full measurable space. -/
theorem trivial_filtration_does_not_generate_bool :
    let filtration : Filtration Nat (⊤ : MeasurableSpace Bool) :=
      Filtration.const Nat (⊥ : MeasurableSpace Bool) bot_le
    (⨆ time : Nat, filtration time) ≠ (⊤ : MeasurableSpace Bool) := by
  dsimp only
  simp only [Filtration.const_apply, iSup_const]
  intro bottom_eq_top
  have singleton_measurable :
      MeasurableSet[(⊥ : MeasurableSpace Bool)] {true} := by
    rw [bottom_eq_top]
    exact MeasurableSet.singleton true
  rw [MeasurableSpace.measurableSet_bot_iff] at singleton_measurable
  rcases singleton_measurable with singleton_empty | singleton_univ
  · exact Set.singleton_ne_empty true singleton_empty
  · have false_mem : false ∈ ({true} : Set Bool) := by
      rw [singleton_univ]
      exact Set.mem_univ false
    exact Bool.false_ne_true (Set.mem_singleton_iff.mp false_mem)

#print axioms trivial_filtration_does_not_generate_bool

/-- With two singular Boolean Dirac laws and prior one half, the bottom
filtration keeps the first-state posterior constant at one half. Thus it does
not converge to one under the first law. -/
theorem filtration_generation_is_necessary :
    let probabilityX : Measure Bool := Measure.dirac true
    let probabilityY : Measure Bool := Measure.dirac false
    let filtration : Filtration Nat (⊤ : MeasurableSpace Bool) :=
      Filtration.const Nat (⊥ : MeasurableSpace Bool) bot_le
    probabilityX ⟂ₘ probabilityY ∧
      ¬ ∀ᵐ transcript ∂probabilityX,
        Tendsto
          (fun time ↦ binaryPosteriorProcess
            (binaryPriorMixture (1 / 2 : Real) probabilityX probabilityY)
            filtration {true} time transcript)
          atTop (𝓝 1) := by
  dsimp only
  constructor
  · refine ⟨{false}, MeasurableSet.singleton false, ?_, ?_⟩ <;> simp
  letI : IsProbabilityMeasure
      (binaryPriorMixture (1 / 2 : Real)
        (Measure.dirac true) (Measure.dirac false)) := by
    rw [isProbabilityMeasure_iff]
    simp only [binaryPriorMixture, Measure.coe_add, Pi.add_apply,
      Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num : (0 : Real) ≤ 1 / 2)
      (by norm_num : (0 : Real) ≤ 1 - 1 / 2)]
    norm_num
  intro convergence_ae
  rw [MeasureTheory.ae_dirac_eq] at convergence_ae
  rw [Filter.eventually_pure] at convergence_ae
  have posterior_eq_half (time : Nat) :
      binaryPosteriorProcess
        (binaryPriorMixture (1 / 2 : Real)
          (Measure.dirac true) (Measure.dirac false))
        (Filtration.const Nat (⊥ : MeasurableSpace Bool) bot_le)
        {true} time true = (1 / 2 : Real) := by
    rw [binaryPosteriorProcess, Filtration.const_apply, MeasureTheory.condExp_bot]
    change (∫ (transcript : Bool),
      ({true} : Set Bool).indicator (1 : Bool → Real) transcript ∂
        binaryPriorMixture (1 / 2 : Real)
          (Measure.dirac true) (Measure.dirac false)) = 1 / 2
    rw [integral_indicator_one (MeasurableSet.singleton true)]
    simp [binaryPriorMixture, measureReal_def]
  have half_tends_to_one :
      Tendsto (fun _ : Nat ↦ (1 / 2 : Real)) atTop (𝓝 1) := by
    simpa only [posterior_eq_half] using convergence_ae
  have half_eq_one : (1 / 2 : Real) = 1 :=
    tendsto_const_nhds_iff.mp half_tends_to_one
  norm_num at half_eq_one

#print axioms filtration_generation_is_necessary

end D5.S3.Observer.MeasureSeparation.SingularPosteriorCollapse
