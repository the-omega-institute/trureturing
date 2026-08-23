/- GID: D5/S3/ConceptDynamics/Control/FiniteHorizonReachability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Control/FiniteHorizonReachability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite winning stages exactly characterize bounded reach strategies. -/

import Mathlib.Data.Set.Basic

/- Library-search audit trail (2026-08-22):
   * Current-tree searches for controlled predecessors, winning regions,
     bounded forcing, and strategy trees found no reusable family primitive.
     `RelationalReachExpansion` is the closest declaration, but it models
     uncontrolled relational reachability rather than state-dependent actions
     with adversarial nondeterministic successors.
   * Pinned Mathlib searches found bounded quiver paths and finite
     combinatorial-game state machinery, but neither has the source semantics.
   * Loogle searches for "winning region" and "reachability game" returned no
     hits. LeanSearch returned only the same unrelated path and game results. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Control.FiniteHorizonReachability

/-- A controlled transition system consists of the actions available at each
state and the nonempty set of possible successors after each action. -/
structure ControlSystem (State : Type*) where
  Action : State -> Type*
  successor : {state : State} -> Action state -> Set State
  successor_nonempty : forall {state} (action : Action state),
    (successor action).Nonempty

/-- States from which one action confines every possible successor to the
target set. -/
def controlPredecessor {State : Type*} (system : ControlSystem State)
    (target : Set State) : Set State :=
  {state | exists action : system.Action state,
    system.successor action ⊆ target}

/-- The finite winning stages start at the goal and repeatedly adjoin the
controlled predecessor of the previous stage. -/
def winningRegion {State : Type*} (system : ControlSystem State)
    (goal : Set State) : Nat -> Set State
  | 0 => goal
  | n + 1 => winningRegion system goal n ∪
      controlPredecessor system (winningRegion system goal n)

/-- A bounded reach strategy either certifies that the current state is
already a goal, or chooses an action and supplies a continuation strategy for
every successor that the environment may select. -/
inductive BoundedReachStrategy {State : Type*} (system : ControlSystem State)
    (goal : Set State) : Nat -> State -> Prop
  | now {n : Nat} {state : State} (at_goal : state ∈ goal) :
      BoundedReachStrategy system goal n state
  | step {n : Nat} {state : State} (action : system.Action state)
      (continuation : forall next, next ∈ system.successor action ->
        BoundedReachStrategy system goal n next) :
      BoundedReachStrategy system goal (n + 1) state

private theorem goal_subset_winningRegion {State : Type*}
    (system : ControlSystem State) (goal : Set State) (n : Nat) :
    goal ⊆ winningRegion system goal n := by
  induction n with
  | zero => exact fun _ atGoal => atGoal
  | succ n inductionHypothesis =>
      intro state atGoal
      exact Or.inl (inductionHypothesis atGoal)

private theorem strategy_budget_succ {State : Type*}
    {system : ControlSystem State} {goal : Set State} {n : Nat} {state : State}
    (strategy : BoundedReachStrategy system goal n state) :
    BoundedReachStrategy system goal (n + 1) state := by
  induction strategy with
  | now atGoal => exact .now atGoal
  | step action continuation inductionHypothesis =>
      exact .step action (fun next isSuccessor =>
        inductionHypothesis next isSuccessor)

/-- A state belongs to the `n`th winning stage exactly when there is a strategy
that guarantees reaching the goal within at most `n` transitions. -/
theorem finite_horizon_reachability {State : Type*}
    (system : ControlSystem State) (goal : Set State) (n : Nat)
    (state : State) :
    state ∈ winningRegion system goal n <->
      BoundedReachStrategy system goal n state := by
  induction n generalizing state with
  | zero =>
      constructor
      · intro atGoal
        exact .now atGoal
      · intro strategy
        cases strategy with
        | now atGoal => exact atGoal
  | succ n inductionHypothesis =>
      constructor
      · intro isWinning
        rcases isWinning with previouslyWinning | oneStepWinning
        · exact strategy_budget_succ
            ((inductionHypothesis state).mp previouslyWinning)
        · rcases oneStepWinning with ⟨action, confinesSuccessors⟩
          exact .step action (fun next isSuccessor =>
            (inductionHypothesis next).mp (confinesSuccessors isSuccessor))
      · intro strategy
        cases strategy with
        | now atGoal =>
            exact goal_subset_winningRegion system goal (n + 1) atGoal
        | step action continuation =>
            exact Or.inr ⟨action, fun _ isSuccessor =>
              (inductionHypothesis _).mpr (continuation _ isSuccessor)⟩

#print axioms finite_horizon_reachability

end D5.S3.ConceptDynamics.Control.FiniteHorizonReachability
