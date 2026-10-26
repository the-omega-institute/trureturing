/- GID: D5/S3/ConceptDynamics/DecisionValue/PartialMenuFiniteHorizonDescent
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DecisionValue/PartialMenuFiniteHorizonDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fiberwise partial menus preserve finite-horizon values, all tied legal actions, and tagged prefix traces. -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! Fiberwise finite partial menus preserve Bellman values, tied legal labels,
and the tagged semantics of every finite action prefix. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent

/-- The result of attempting a named action.  A failure is a tagged report,
and is kept distinct from a successful output. -/
inductive ActionResult (State Output Failure : Type*) where
  | success (output : Output) (cost : Real) (next : State)
  | failure (report : Failure) (cost : Real)

/-- A finite prefix record retains every successful output, total cost, every
failure report, and the final state when the prefix never fails. -/
structure PrefixRecord (State Output Failure : Type*) where
  outputs : List Output
  totalCost : Real
  failures : List Failure
  finalState : Option State

private def PrefixRecord.prependSuccess
    {State Output Failure : Type*} (output : Output) (cost : Real)
    (rest : PrefixRecord State Output Failure) : PrefixRecord State Output Failure :=
  { outputs := output :: rest.outputs
    totalCost := cost + rest.totalCost
    failures := rest.failures
    finalState := rest.finalState }

/-- Execute a fixed action word.  The first failure terminates the run and is
recorded; successful prefixes remain in the returned output and cost fields. -/
def runPrefix {State Action Output Failure : Type*}
    (step : State → Action → ActionResult State Output Failure) :
    State → List Action → PrefixRecord State Output Failure
  | state, [] =>
      { outputs := [], totalCost := 0, failures := [], finalState := some state }
  | state, action :: actions =>
      match step state action with
      | .success output cost next =>
          PrefixRecord.prependSuccess output cost (runPrefix step next actions)
      | .failure report cost =>
          { outputs := [], totalCost := cost, failures := [report], finalState := none }

/-- Push a prefix record through an abstraction, preserving output, cost, and
failure fields and mapping only a successful final state. -/
def PrefixRecord.mapState {State MacroState Output Failure : Type*}
    (abstract : State → MacroState) (record : PrefixRecord State Output Failure) :
    PrefixRecord MacroState Output Failure :=
  { outputs := record.outputs
    totalCost := record.totalCost
    failures := record.failures
    finalState := record.finalState.map abstract }

private def ActionResult.mapState {State MacroState Output Failure : Type*}
    (abstract : State → MacroState) :
    ActionResult State Output Failure → ActionResult MacroState Output Failure
  | .success output cost next => .success output cost (abstract next)
  | .failure report cost => .failure report cost

private theorem PrefixRecord.mapState_prependSuccess
    {State MacroState Output Failure : Type*}
    (abstract : State → MacroState) (output : Output) (cost : Real)
    (record : PrefixRecord State Output Failure) :
    PrefixRecord.mapState abstract (PrefixRecord.prependSuccess output cost record) =
      PrefixRecord.prependSuccess output cost (PrefixRecord.mapState abstract record) := rfl

/-- A partial decision system keeps a finite nonempty legal menu at every
state.  The fields outside the menu are still present only to describe the
tagged failure semantics of an attempted illegal action. -/
structure PartialMenuModel (State Action Output Failure : Type*) where
  menu : State → Finset Action
  menuNonempty : ∀ state, (menu state).Nonempty
  successor : Action → State → State
  reward : State → Action → Real
  terminal : State → Real
  output : State → Action → Output
  successCost : State → Action → Real
  failureReport : State → Action → Failure
  failureCost : State → Action → Real

/-- Legal actions use the success branch; every other named action remains a
failure and is never inserted into the legal menu. -/
noncomputable def PartialMenuModel.step {State Action Output Failure : Type*}
    (model : PartialMenuModel State Action Output Failure)
    (state : State) (action : Action) : ActionResult State Output Failure :=
  by
    classical
    exact if h : action ∈ model.menu state then
      .success (model.output state action) (model.successCost state action)
        (model.successor action state)
    else
      .failure (model.failureReport state action) (model.failureCost state action)

/-- Bellman value with a state-dependent finite legal menu. -/
noncomputable def partialHorizonValue
    {State Action : Type*}
    (menu : State → Finset Action)
    (menuNonempty : ∀ state, (menu state).Nonempty)
    (successor : Action → State → State)
    (reward : State → Action → Real)
    (terminal : State → Real) : Nat → State → Real
  | 0 => terminal
  | n + 1 => fun state =>
      (menu state).sup' (menuNonempty state) (fun action =>
        reward state action +
          partialHorizonValue menu menuNonempty successor reward terminal n
            (successor action state))

/-- All legal labels attaining the finite-horizon Bellman maximum. -/
def partialHorizonOptimalActions
    {State Action : Type*}
    (menu : State → Finset Action)
    (menuNonempty : ∀ state, (menu state).Nonempty)
    (successor : Action → State → State)
    (reward : State → Action → Real)
    (terminal : State → Real)
    (horizon : Nat) (state : State) : Set Action :=
  {action | action ∈ menu state ∧
    ∀ alternative, alternative ∈ menu state →
      reward state alternative +
          partialHorizonValue menu menuNonempty successor reward terminal horizon
            (successor alternative state) ≤
        reward state action +
          partialHorizonValue menu menuNonempty successor reward terminal horizon
            (successor action state)}

/-- Fiberwise partial menus preserve Bellman values, every tied legal action,
and the complete tagged trace of every finite action prefix.  The menu
equality transports legal labels. Success data need factor only on legal
actions and failure data only on illegal actions; unused branch data are
unconstrained. Terminal values factor at every state. -/
theorem partial_menu_finite_horizon_descent
    {MicroState MacroState Action Output Failure : Type*}
    (abstract : MicroState → MacroState)
    (micro : PartialMenuModel MicroState Action Output Failure)
    (macroModel : PartialMenuModel MacroState Action Output Failure)
    (menuFactors : ∀ state, micro.menu state = macroModel.menu (abstract state))
    (successorFactors : ∀ action state, action ∈ micro.menu state →
      abstract (micro.successor action state) =
        macroModel.successor action (abstract state))
    (rewardFactors : ∀ state action, action ∈ micro.menu state →
      micro.reward state action = macroModel.reward (abstract state) action)
    (terminalFactors : ∀ state,
      micro.terminal state = macroModel.terminal (abstract state))
    (outputFactors : ∀ state action, action ∈ micro.menu state →
      micro.output state action = macroModel.output (abstract state) action)
    (successCostFactors : ∀ state action, action ∈ micro.menu state →
      micro.successCost state action = macroModel.successCost (abstract state) action)
    (failureReportFactors : ∀ state action, action ∉ micro.menu state →
      micro.failureReport state action = macroModel.failureReport (abstract state) action)
    (failureCostFactors : ∀ state action, action ∉ micro.menu state →
      micro.failureCost state action = macroModel.failureCost (abstract state) action) :
    (∀ horizon state,
      partialHorizonValue micro.menu micro.menuNonempty micro.successor micro.reward
          micro.terminal horizon state =
        partialHorizonValue macroModel.menu macroModel.menuNonempty macroModel.successor macroModel.reward
          macroModel.terminal horizon (abstract state)) ∧
    (∀ horizon state,
      partialHorizonOptimalActions micro.menu micro.menuNonempty micro.successor
          micro.reward micro.terminal horizon state =
        partialHorizonOptimalActions macroModel.menu macroModel.menuNonempty macroModel.successor
          macroModel.reward macroModel.terminal horizon (abstract state)) ∧
    (∀ state actions,
      PrefixRecord.mapState abstract
          (runPrefix micro.step state actions) =
        runPrefix macroModel.step (abstract state) actions) := by
  have valueFactors : ∀ horizon state,
      partialHorizonValue micro.menu micro.menuNonempty micro.successor micro.reward
          micro.terminal horizon state =
        partialHorizonValue macroModel.menu macroModel.menuNonempty macroModel.successor macroModel.reward
          macroModel.terminal horizon (abstract state) := by
    intro horizon
    induction horizon with
    | zero =>
        intro state
        exact terminalFactors state
    | succ horizon inductionHypothesis =>
        intro state
        simp only [partialHorizonValue]
        apply Finset.sup'_congr (micro.menuNonempty state) (menuFactors state)
        intro action actionLegal
        rw [rewardFactors state action actionLegal,
          inductionHypothesis (micro.successor action state),
          successorFactors action state actionLegal]
  have scoreFactors : ∀ horizon state action, action ∈ micro.menu state →
      micro.reward state action +
          partialHorizonValue micro.menu micro.menuNonempty micro.successor micro.reward
            micro.terminal horizon (micro.successor action state) =
        macroModel.reward (abstract state) action +
          partialHorizonValue macroModel.menu macroModel.menuNonempty macroModel.successor macroModel.reward
            macroModel.terminal horizon (macroModel.successor action (abstract state)) := by
    intro horizon state action actionLegal
    rw [rewardFactors state action actionLegal,
      valueFactors horizon (micro.successor action state),
      successorFactors action state actionLegal]
  have optimalFactors : ∀ horizon state,
      partialHorizonOptimalActions micro.menu micro.menuNonempty micro.successor
          micro.reward micro.terminal horizon state =
        partialHorizonOptimalActions macroModel.menu macroModel.menuNonempty macroModel.successor
          macroModel.reward macroModel.terminal horizon (abstract state) := by
    intro horizon state
    apply Set.ext
    intro action
    simp only [partialHorizonOptimalActions, Set.mem_setOf_eq]
    constructor
    · rintro ⟨actionLegal, actionOptimal⟩
      refine ⟨by simpa only [menuFactors state] using actionLegal, ?_⟩
      intro alternative alternativeLegal
      have alternativeMicro : alternative ∈ micro.menu state := by
        rwa [menuFactors state]
      rw [← scoreFactors horizon state alternative alternativeMicro,
        ← scoreFactors horizon state action actionLegal]
      exact actionOptimal alternative alternativeMicro
    · rintro ⟨actionLegal, actionOptimal⟩
      have actionMicro : action ∈ micro.menu state := by rwa [menuFactors state]
      refine ⟨actionMicro, ?_⟩
      intro alternative alternativeLegal
      rw [scoreFactors horizon state alternative alternativeLegal,
        scoreFactors horizon state action actionMicro]
      exact actionOptimal alternative (by simpa only [menuFactors state] using alternativeLegal)
  have stepFactors : ∀ state action,
      ActionResult.mapState abstract (micro.step state action) =
        macroModel.step (abstract state) action := by
    intro state action
    unfold PartialMenuModel.step
    by_cases h : action ∈ micro.menu state
    · have hmacro : action ∈ macroModel.menu (abstract state) := by
        simpa only [menuFactors state] using h
      simp only [dif_pos h, dif_pos hmacro]
      simp [ActionResult.mapState, outputFactors state action h,
        successCostFactors state action h, successorFactors action state h]
    · have hmacro : action ∉ macroModel.menu (abstract state) := by
        simpa only [menuFactors state] using h
      simp only [dif_neg h, dif_neg hmacro]
      simp [ActionResult.mapState, failureReportFactors state action h,
        failureCostFactors state action h]
  have prefixFactors : ∀ state actions,
      PrefixRecord.mapState abstract (runPrefix micro.step state actions) =
        runPrefix macroModel.step (abstract state) actions := by
    intro state actions
    induction actions generalizing state with
    | nil => rfl
    | cons action actions inductionHypothesis =>
        cases hstep : micro.step state action with
        | success output cost next =>
            have hmacro : macroModel.step (abstract state) action =
                .success output cost (abstract next) := by
              rw [← stepFactors state action, hstep]
              rfl
            simp only [runPrefix, hstep, hmacro]
            rw [PrefixRecord.mapState_prependSuccess, inductionHypothesis next]
        | failure report cost =>
            have hmacro : macroModel.step (abstract state) action =
                .failure report cost := by
              rw [← stepFactors state action, hstep]
              rfl
            simp only [runPrefix, hstep, hmacro, PrefixRecord.mapState, Option.map,
              ActionResult.mapState]
  exact ⟨valueFactors, optimalFactors, prefixFactors⟩

#print axioms partial_menu_finite_horizon_descent

end D5.S3.ConceptDynamics.DecisionValue.PartialMenuFiniteHorizonDescent
