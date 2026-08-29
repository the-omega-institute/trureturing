/- GID: D5/S3/ConceptDynamics/Interpretation/FreshIndependentCheckpointGuarantee
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Interpretation/FreshIndependentCheckpointGuarantee
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fresh product-law checkpoints bound bad all-pass certification mass. -/

import D5.S3.TotalVariation.IndependentSamplingExponentialBound
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-29):
   * Body-shape searches found the Boolean witness modules in the interpretation
     family, but no general theorem for a frozen implementation on a countable
     deployment carrier.
   * The existing Boolean joint-law definition is specialized to `Bool`, so it
     is not reused as the carrier of this general source clause.
   * Exact pinned-Mathlib hits `Measure.pi_pi`, `ENNReal.toReal_prod`, and
     `probReal_add_probReal_compl` evaluate the product-law all-pass event.
   * The exact repository hit `independent_sampling_exponential_bound` supplies
     the final exponential estimate and is applied directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.Interpretation.FreshIndependentCheckpointGuarantee

open MeasureTheory Set
open D5.S3.TotalVariation.IndependentSamplingExponentialBound

/-- An arbitrary implementation fixed before seeing its checkpoints receives
the deployment guarantee from the actual joint product law. The first public
conjunct evaluates the all-pass probability; the second bounds it whenever the
deployment loss is at least `epsilon`. -/
theorem fresh_independent_checkpoint_deployment_guarantee
    {Input Output : Type*}
    [MeasurableSpace Input] [MeasurableSingletonClass Input] [Countable Input]
    (deployment : PMF Input)
    (implementation expected : Input -> Output)
    (m : Nat) (epsilon : Real)
    (epsilonNonnegative : 0 <= epsilon)
    (epsilonAtMostOne : epsilon <= 1)
    (lossAtLeast :
      epsilon <= deployment.toMeasure.real
        {input | implementation input ≠ expected input}) :
    let suiteLaw : Measure (Fin m -> Input) :=
      Measure.pi (fun _ : Fin m => deployment.toMeasure)
    let allPass : Set (Fin m -> Input) :=
      {suite | forall index, implementation (suite index) = expected (suite index)}
    suiteLaw.real allPass =
        (deployment.toMeasure.real
          {input | implementation input = expected input}) ^ m /\
      suiteLaw.real allPass <= Real.exp (-(epsilon * (m : Real))) := by
  dsimp only
  let passSet : Set Input :=
    {input | implementation input = expected input}
  let failureSet : Set Input :=
    {input | implementation input ≠ expected input}
  let allPass : Set (Fin m -> Input) :=
    {suite | forall index, implementation (suite index) = expected (suite index)}
  have passMeasurable : MeasurableSet passSet :=
    Set.to_countable passSet |>.measurableSet
  have failureMeasurable : MeasurableSet failureSet :=
    Set.to_countable failureSet |>.measurableSet
  have allPassRectangle :
      allPass = Set.pi Set.univ (fun _ : Fin m => passSet) := by
    ext suite
    simp [allPass, passSet]
  have exactMass :
      (Measure.pi (fun _ : Fin m => deployment.toMeasure)).real allPass =
        (deployment.toMeasure.real passSet) ^ m := by
    rw [measureReal_def, allPassRectangle, Measure.pi_pi, ENNReal.toReal_prod]
    simp [measureReal_def]
  have passIsFailureComplement : passSet = failureSetᶜ := by
    ext input
    simp [passSet, failureSet]
  have passMass :
      deployment.toMeasure.real passSet =
        1 - deployment.toMeasure.real failureSet := by
    have massSum := probReal_add_probReal_compl
      (μ := deployment.toMeasure) failureMeasurable
    rw [← passIsFailureComplement] at massSum
    linarith
  have passAtMost : deployment.toMeasure.real passSet <= 1 - epsilon := by
    rw [passMass]
    change epsilon <= deployment.toMeasure.real failureSet at lossAtLeast
    linarith
  refine ⟨by simpa [allPass, passSet] using exactMass, ?_⟩
  rw [show
    (Measure.pi (fun _ : Fin m => deployment.toMeasure)).real
        {suite | forall index,
          implementation (suite index) = expected (suite index)} =
      (deployment.toMeasure.real passSet) ^ m by
        simpa [allPass] using exactMass]
  exact (pow_le_pow_left₀ measureReal_nonneg passAtMost m).trans
    (independent_sampling_exponential_bound epsilon m
      epsilonNonnegative epsilonAtMostOne)

#print axioms fresh_independent_checkpoint_deployment_guarantee

end D5.S3.ConceptDynamics.Interpretation.FreshIndependentCheckpointGuarantee
