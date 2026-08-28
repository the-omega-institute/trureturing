/- GID: D5/S3/Estimation/DataProcessing/UniversalBeliefDecisionSufficiency
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/UniversalBeliefDecisionSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal beliefs give equal Bayes values for every future policy and decision problem. -/

import D5.S3.Estimation.SequentialDecisionRisk.TaskIndependentBeliefSufficiency

/- Library-search audit trail (2026-08-26):
   * The frozen predecessor states the exact source theorem on arbitrary measurable
     hidden and future carriers, but was withdrawn solely for placement. The redo
     mandate requires a fresh GID while leaving that module untouched.
   * The imported predecessor and Mathlib are the single source of truth for
     probability measures, Markov kernels, lintegrals, and the decision-rule
     infimum. No local carrier, law, `def`, or `abbrev` is introduced.
   * Pinned Mathlib has no full task-independent Bayes-sufficiency declaration.
     The frozen repository theorem is applied directly rather than reproved. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open D5.S3.Estimation.SequentialDecisionRisk.TaskIndependentBeliefSufficiency renaming
  task_independent_belief_sufficiency → frozen_task_independent_belief_sufficiency

noncomputable section

namespace D5.S3.Estimation.DataProcessing.UniversalBeliefDecisionSufficiency

universe u

/-- Equality of history beliefs preserves Bayes value simultaneously for every
future experiment policy, action carrier, loss, and transcript-dependent
decision rule. -/
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
  change
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
          ∂(posterior history' : Measure Hidden)
  exact frozen_task_independent_belief_sufficiency
    posterior futureExperimentLaw equalPosterior

#print axioms task_independent_belief_sufficiency

end D5.S3.Estimation.DataProcessing.UniversalBeliefDecisionSufficiency
