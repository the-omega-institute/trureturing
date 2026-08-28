/- GID: D5/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValueScale/FiniteHorizonValueFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compatible abstract dynamics factor every finite-horizon Bellman value. -/

import D5.S3.ConceptDynamics.DecisionValue.FiniteHorizonOptimalActionDescent

/- Library-search audit trail (2026-08-27):
   * The imported family owns the canonical `finiteHorizonValue` construction
     from transitions, stage rewards, terminal values, and finite maxima.
   * Its exact value-factorization result is a private helper, so it cannot be
     a receipt target or be applied from this module.
   * Repository searches found no public theorem with this value equality.
     Pinned Mathlib's `Finset.sup'_congr` is the exact finite-maximum bridge
     used in the successor step; no full-statement library theorem matched. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValueScale.FiniteHorizonValueFactorization

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.DecisionValue.FiniteHorizonOptimalActionDescent

/-- If transitions commute with an abstraction and both stage rewards and the
terminal value factor through it, every finite-horizon Bellman value factors
through the same abstraction. -/
theorem finite_horizon_value_factorization
    {MicroState MacroState Action : Type*}
    [Fintype Action] [Nonempty Action]
    (abstract : Concept MicroState MacroState)
    (microTransition : Action -> MicroState -> MicroState)
    (macroTransition : Action -> MacroState -> MacroState)
    (microReward : MicroState -> Action -> Real)
    (macroReward : MacroState -> Action -> Real)
    (microTerminal : MicroState -> Real)
    (macroTerminal : MacroState -> Real)
    (transitionCompatible : forall action state,
      abstract (microTransition action state) =
        macroTransition action (abstract state))
    (rewardFactors : forall state action,
      microReward state action = macroReward (abstract state) action)
    (terminalFactors : forall state,
      microTerminal state = macroTerminal (abstract state)) :
    forall horizon,
      finiteHorizonValue microTransition microReward microTerminal horizon =
        finiteHorizonValue macroTransition macroReward macroTerminal horizon ∘
          abstract := by
  intro horizon
  induction horizon with
  | zero =>
      funext state
      simpa [finiteHorizonValue, Function.comp_apply] using terminalFactors state
  | succ horizon inductionHypothesis =>
      funext state
      simp only [finiteHorizonValue, Function.comp_apply]
      apply Finset.sup'_congr Finset.univ_nonempty rfl
      intro action _
      rw [rewardFactors state action,
        congrFun inductionHypothesis (microTransition action state)]
      simp only [Function.comp_apply]
      rw [transitionCompatible action state]

#print axioms finite_horizon_value_factorization

end D5.S3.ConceptDynamics.DecisionValueScale.FiniteHorizonValueFactorization
