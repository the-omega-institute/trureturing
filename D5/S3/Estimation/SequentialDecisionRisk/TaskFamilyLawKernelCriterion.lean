/- GID: D5/S3/Estimation/SequentialDecisionRisk/TaskFamilyLawKernelCriterion
   generality: G
   mirror-B: D5/B/S3/Estimation/SequentialDecisionRisk/TaskFamilyLawKernelCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Separating losses identify laws; finite event indicators identify PMFs. -/

import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-28):
   * `PredictiveRiskOptimizerHierarchy` is the canonical finite-PMF risk
     family, but proves only the forward kernel hierarchy and has no event-
     indicator clause, so it is not an exact bind target.
   * D5 searches for measure-determining families, risk-kernel equality, and
     event-indicator separation found no exact declaration.
   * Pinned Mathlib supplies `PMF.ext`, `PMF.apply_ne_top`, and finite sums;
     no exact theorem combines the source's two clauses.
   * A body-shape search found only the finite-PMF `riskProfile`. This module
     introduces no `def` or `abbrev`; its general risk map is constructed
     directly from the supplied law, expectation, and loss primitives. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Estimation.SequentialDecisionRisk.TaskFamilyLawKernelCriterion

/-- A loss family that determines every allowed law makes risk equivalence
exactly predictive-law equivalence. Independently, on a finite outcome space,
agreement of the expectations of all event indicators determines a PMF. -/
theorem task_family_law_kernel_criterion
    {History Law Outcome Loss Action FiniteOutcome : Type*}
    [Fintype FiniteOutcome]
    (predictiveLaw : History -> Law)
    (expectation : Law -> (Outcome -> Real) -> Real)
    (loss : Loss -> Action -> Outcome -> Real)
    (measureDetermining :
      forall first second : Law,
        (forall task action,
          expectation first (loss task action) =
            expectation second (loss task action)) ->
        first = second) :
    Setoid.ker predictiveLaw =
        Setoid.ker (fun history task action =>
          expectation (predictiveLaw history) (loss task action)) /\
      forall first second : PMF FiniteOutcome,
        (forall event : Set FiniteOutcome,
          (∑ outcome, event.indicator (fun y => (first y).toReal) outcome) =
            ∑ outcome, event.indicator (fun y => (second y).toReal) outcome) ->
        first = second := by
  classical
  constructor
  · apply Setoid.ext
    intro history history'
    constructor
    · intro equalLaw
      change predictiveLaw history = predictiveLaw history' at equalLaw
      change
        (fun task action =>
          expectation (predictiveLaw history) (loss task action)) =
        fun task action =>
          expectation (predictiveLaw history') (loss task action)
      rw [equalLaw]
    · intro equalRisk
      change
        (fun task action =>
          expectation (predictiveLaw history) (loss task action)) =
        (fun task action =>
          expectation (predictiveLaw history') (loss task action)) at equalRisk
      change predictiveLaw history = predictiveLaw history'
      apply measureDetermining
      intro task action
      exact congrFun (congrFun equalRisk task) action
  · intro first second equalIndicatorRisk
    apply PMF.ext
    intro outcome
    rw [← ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top first outcome) (PMF.apply_ne_top second outcome)]
    simpa using equalIndicatorRisk ({outcome} : Set FiniteOutcome)

#print axioms task_family_law_kernel_criterion

end D5.S3.Estimation.SequentialDecisionRisk.TaskFamilyLawKernelCriterion
