/- GID: D5/S3/Estimation/SequentialDecisionRisk/TaskIndependentBeliefSufficiency
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/TaskIndependentBeliefSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal beliefs give equal Bayes values for every future policy and decision problem. -/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Basic

/- Library-search audit trail (2026-08-26):
   * The frozen `posterior_future_policy_universal_sufficiency` has the exact
     finite-state conclusion, but its `[Fintype Theta]` carrier omits the
     source's standard-Borel branch and is therefore not an exact bind.
   * `posterior_history_compression` allows arbitrary measurable hidden states,
     but its policy-cost clause does not expose the policy-conditioned future
     transcript and terminal decision rule together. The other nearby quotient
     theorems concern static prediction or canonical quotient minimality.
   * Body-shape searches for nested lintegrals under a decision-rule infimum
     found no existing D5 declaration. Pinned Mathlib supplies the canonical
     probability-measure, Markov-kernel, lintegral, and infimum primitives used
     directly below. No `def` or `abbrev` is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace D5.S3.Estimation.SequentialDecisionRisk.TaskIndependentBeliefSufficiency

universe u

/-- A history belief is sufficient simultaneously for every future experiment
policy and every Bayes decision problem. A policy is represented by its Markov
kernel from the hidden state to the complete future transcript, and terminal
decisions may depend on that entire transcript. -/
theorem task_independent_belief_sufficiency
    {Hidden History Policy Future : Type*}
    [MeasurableSpace Hidden] [MeasurableSpace Future]
    (posterior : History -> ProbabilityMeasure Hidden)
    (futureExperimentLaw :
      Policy -> {kernel : Kernel Hidden Future // IsMarkovKernel kernel})
    {history history' : History}
    (equalPosterior : posterior history = posterior history') :
    ∀ (policy : Policy) (Action : Type u) (loss : Hidden -> Action -> ENNReal),
      (⨅ decision : Future -> Action,
        ∫⁻ hidden,
          ∫⁻ future, loss hidden (decision future)
            ∂(futureExperimentLaw policy).1 hidden
          ∂(posterior history : Measure Hidden)) =
      ⨅ decision : Future -> Action,
        ∫⁻ hidden,
          ∫⁻ future, loss hidden (decision future)
            ∂(futureExperimentLaw policy).1 hidden
          ∂(posterior history' : Measure Hidden) := by
  intro policy Action loss
  rw [equalPosterior]

#print axioms task_independent_belief_sufficiency

end D5.S3.Estimation.SequentialDecisionRisk.TaskIndependentBeliefSufficiency
