/- GID: D5/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/FiniteHorizonOptimalActionDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Exact causal abstraction preserves every finite-horizon optimal-action set. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/- Library-search audit trail (2026-08-23):
   * Current-tree searches for finite-horizon values, optimal-action sets,
     Bellman recurrences, stage rewards, and semantic `_eq_` bridges found no
     equivalent ConceptDynamics family primitive or theorem.
   * The observer `finitePredictionDistance` is a single-update distance
     recurrence, and `FiniteHorizonReachability` is an adversarial reachability
     system; neither has the controlled reward semantics used here.
   * The canonical `Concept` carrier is imported and used directly. Pinned
     Mathlib's exact `Finset.sup'_congr` and `Finset.univ_nonempty` declarations
     construct and compare the finite maxima below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.FiniteHorizonOptimalActionDescent

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The finite-horizon Bellman value constructed from a controlled transition,
stage reward, and terminal value. -/
noncomputable def finiteHorizonValue {State Action : Type*}
    [Fintype Action] [Nonempty Action]
    (transition : Action -> State -> State)
    (reward : State -> Action -> Real) (terminalValue : State -> Real) :
    Nat -> State -> Real
  | 0 => terminalValue
  | n + 1 => fun state =>
      Finset.univ.sup'
        Finset.univ_nonempty
        (fun action => reward state action +
          finiteHorizonValue transition reward terminalValue n
            (transition action state))

/-- Actions maximizing the next Bellman step after `n` continuation stages. -/
def finiteHorizonOptimalActions {State Action : Type*}
    [Fintype Action] [Nonempty Action]
    (transition : Action -> State -> State)
    (reward : State -> Action -> Real) (terminalValue : State -> Real)
    (n : Nat) (state : State) : Set Action :=
  {action | forall alternative,
    reward state alternative +
        finiteHorizonValue transition reward terminalValue n
          (transition alternative state) <=
      reward state action +
        finiteHorizonValue transition reward terminalValue n
          (transition action state)}

private theorem finite_horizon_value_factors
    {MicroState MacroState Action : Type*}
    [Fintype Action] [Nonempty Action]
    (abstract : Concept MicroState MacroState)
    (microTransition : Action -> MicroState -> MicroState)
    (macroTransition : Action -> MacroState -> MacroState)
    (microReward : MicroState -> Action -> Real)
    (macroReward : MacroState -> Action -> Real)
    (microTerminal : MicroState -> Real)
    (macroTerminal : MacroState -> Real)
    (htransition : forall action state,
      abstract (microTransition action state) =
        macroTransition action (abstract state))
    (hreward : forall state action,
      microReward state action = macroReward (abstract state) action)
    (hterminal : forall state,
      microTerminal state = macroTerminal (abstract state)) :
    forall n state,
      finiteHorizonValue microTransition microReward microTerminal n state =
        finiteHorizonValue macroTransition macroReward macroTerminal n
          (abstract state) := by
  intro n
  induction n with
  | zero =>
      intro state
      simpa [finiteHorizonValue] using hterminal state
  | succ n inductionHypothesis =>
      intro state
      simp only [finiteHorizonValue]
      apply Finset.sup'_congr Finset.univ_nonempty rfl
      intro action _
      rw [hreward state action,
        inductionHypothesis (microTransition action state),
        htransition action state]

/-- If controlled transitions commute with an abstraction and both stage and
terminal rewards factor through it, then the micro and macro maximizing-action
sets agree at every finite horizon. Thus the action set depends only on the
abstract concept value. -/
theorem finite_horizon_optimal_actions_descend
    {MicroState MacroState Action : Type*}
    [Fintype Action] [Nonempty Action]
    (abstract : Concept MicroState MacroState)
    (microTransition : Action -> MicroState -> MicroState)
    (macroTransition : Action -> MacroState -> MacroState)
    (microReward : MicroState -> Action -> Real)
    (macroReward : MacroState -> Action -> Real)
    (microTerminal : MicroState -> Real)
    (macroTerminal : MacroState -> Real)
    (htransition : forall action state,
      abstract (microTransition action state) =
        macroTransition action (abstract state))
    (hreward : forall state action,
      microReward state action = macroReward (abstract state) action)
    (hterminal : forall state,
      microTerminal state = macroTerminal (abstract state)) :
    forall n state,
      finiteHorizonOptimalActions microTransition microReward microTerminal n state =
        finiteHorizonOptimalActions macroTransition macroReward macroTerminal n
          (abstract state) := by
  intro n state
  apply Set.ext
  intro action
  simp only [finiteHorizonOptimalActions, Set.mem_setOf_eq]
  have hscore (chosen : Action) :
      microReward state chosen +
          finiteHorizonValue microTransition microReward microTerminal n
            (microTransition chosen state) =
        macroReward (abstract state) chosen +
          finiteHorizonValue macroTransition macroReward macroTerminal n
            (macroTransition chosen (abstract state)) := by
    rw [hreward state chosen,
      finite_horizon_value_factors abstract microTransition macroTransition
        microReward macroReward microTerminal macroTerminal htransition hreward
        hterminal n (microTransition chosen state),
      htransition chosen state]
  constructor
  · intro hoptimal alternative
    calc
      macroReward (abstract state) alternative +
          finiteHorizonValue macroTransition macroReward macroTerminal n
            (macroTransition alternative (abstract state)) =
        microReward state alternative +
          finiteHorizonValue microTransition microReward microTerminal n
            (microTransition alternative state) := (hscore alternative).symm
      _ <= microReward state action +
          finiteHorizonValue microTransition microReward microTerminal n
            (microTransition action state) := hoptimal alternative
      _ = macroReward (abstract state) action +
          finiteHorizonValue macroTransition macroReward macroTerminal n
            (macroTransition action (abstract state)) := hscore action
  · intro hoptimal alternative
    calc
      microReward state alternative +
          finiteHorizonValue microTransition microReward microTerminal n
            (microTransition alternative state) =
        macroReward (abstract state) alternative +
          finiteHorizonValue macroTransition macroReward macroTerminal n
            (macroTransition alternative (abstract state)) := hscore alternative
      _ <= macroReward (abstract state) action +
          finiteHorizonValue macroTransition macroReward macroTerminal n
            (macroTransition action (abstract state)) := hoptimal alternative
      _ = microReward state action +
          finiteHorizonValue microTransition microReward microTerminal n
            (microTransition action state) := (hscore action).symm

#print axioms finite_horizon_optimal_actions_descend

end D5.S3.ConceptDynamics.DecisionValue.FiniteHorizonOptimalActionDescent
