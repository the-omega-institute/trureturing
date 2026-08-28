/- GID: D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality
   generality: G
   mirror-B: D5/B/S3/Observer/DynamicProgramming/StationaryPolicyOptimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Greedy policies are optimal at zero discount; reachable-only greed can fail globally. -/

import D5.S3.Observer.DynamicProgramming.DiscountedBellmanContraction

/- Library-search audit trail (2026-08-25):
   * Repository searches for stationary policies, policy values, greedy Bellman choices,
     and fixed policy operators found no theorem connecting greed to discounted value equality.
   * `discounted_bellman_contraction_and_unique_fixed_point` gives exactly the fixed-point
     uniqueness used below; it has no policy-level optimality conclusion.
   * `bellman_contraction_unique_fixed_point_and_iteration_bound` is an abstract value result,
     while the decision modules concern one-step argmin sets rather than stationary values.
   * Two local Mathlib smart searches for discounted MDP stationary-policy optimality returned
     no declaration. Pinned Mathlib supplies only the contraction and finite-order primitives.
   * This module explicitly downgrades belief-state control to a finite-state ordinary MDP. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.DynamicProgramming.StationaryPolicyOptimality

open scoped BoundedContinuousFunction

open D5.S3.Observer.DynamicProgramming.DiscountedBellmanContraction

/-- A stationary policy chooses one action from the current state, with no time dependence. -/
def StationaryPolicy (State Action : Type*) := State -> Action

/-- A finite transition array is stochastic when every row is nonnegative and sums to one. -/
def IsStochasticTransition {State Action : Type*} [Fintype State]
    (transition : State -> Action -> State -> Real) : Prop :=
  (forall state action nextState, 0 <= transition state action nextState) /\
    forall state action, (Finset.univ.sum fun nextState =>
      transition state action nextState) = 1

/-- The discounted loss Bellman operator, defined by sign-conjugating the existing
reward-maximizing operator. Its pointwise finite minimum is exposed by the theorem below. -/
noncomputable def discountedLossBellmanOperator {State Action : Type*}
    [Fintype State] [TopologicalSpace State] [DiscreteTopology State]
    [Fintype Action] [Nonempty Action]
    (loss : State -> Action -> Real)
    (transition : State -> Action -> State -> Real)
    (gamma : NNReal) (value : State →ᵇ Real) : State →ᵇ Real :=
  -discountedBellmanOperator (fun state action => -loss state action)
    transition gamma (-value)

/-- The Bellman operator after fixing one stationary policy. -/
noncomputable def stationaryPolicyBellmanOperator {State Action : Type*}
    [Fintype State] [TopologicalSpace State] [DiscreteTopology State]
    (loss : State -> Action -> Real)
    (transition : State -> Action -> State -> Real)
    (gamma : NNReal) (policy : StationaryPolicy State Action)
    (value : State →ᵇ Real) : State →ᵇ Real :=
  discountedLossBellmanOperator
    (fun state (_ : Unit) => loss state (policy state))
    (fun state (_ : Unit) nextState =>
      transition state (policy state) nextState) gamma value

/-- A policy is Bellman-greedy at a value when its chosen action realizes the full
Bellman minimum at every state. -/
def IsBellmanGreedy {State Action : Type*}
    [Fintype State] [TopologicalSpace State] [DiscreteTopology State]
    [Fintype Action] [Nonempty Action]
    (loss : State -> Action -> Real)
    (transition : State -> Action -> State -> Real)
    (gamma : NNReal) (policy : StationaryPolicy State Action)
    (value : State →ᵇ Real) : Prop :=
  forall state,
    stationaryPolicyBellmanOperator loss transition gamma policy value state =
      discountedLossBellmanOperator loss transition gamma value state

/-- A stationary policy is globally optimal when its value equals the optimal value
at every state. The policy argument records which policy owns the first value. -/
def IsOptimalStationaryPolicy {State Action : Type*}
    [TopologicalSpace State]
    (_policy : StationaryPolicy State Action)
    (policyValue optimalValue : State →ᵇ Real) : Prop :=
  policyValue = optimalValue

/-- Reachability from one initial state follows positive-probability transitions under
the fixed stationary policy, including the initial state by reflexivity. -/
def PolicyReachable {State Action : Type*}
    (transition : State -> Action -> State -> Real)
    (policy : StationaryPolicy State Action) (start target : State) : Prop :=
  Relation.ReflTransGen
    (fun state nextState => 0 < transition state (policy state) nextState)
    start target

/-- The sign-conjugated loss operator is exactly the finite action minimum of immediate
loss plus discounted expected continuation value. -/
theorem discounted_loss_bellman_operator_apply
    {State Action : Type*}
    [Fintype State] [TopologicalSpace State] [DiscreteTopology State]
    [Fintype Action] [Nonempty Action]
    (loss : State -> Action -> Real)
    (transition : State -> Action -> State -> Real)
    (gamma : NNReal) (value : State →ᵇ Real) (state : State) :
    discountedLossBellmanOperator loss transition gamma value state =
      Finset.univ.inf' Finset.univ_nonempty (fun action =>
        loss state action + (gamma : Real) *
          Finset.univ.sum (fun nextState =>
            transition state action nextState * value nextState)) := by
  let actionCost : Action -> Real := fun action =>
    loss state action + (gamma : Real) *
      Finset.univ.sum (fun nextState =>
        transition state action nextState * value nextState)
  have actionNeg (action : Action) :
      -loss state action + (gamma : Real) *
          Finset.univ.sum (fun nextState =>
            transition state action nextState * (-value nextState)) =
        -actionCost action := by
    have sumNeg :
        Finset.univ.sum (fun nextState =>
            transition state action nextState * (-value nextState)) =
          -(Finset.univ.sum fun nextState =>
            transition state action nextState * value nextState) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro nextState _
      ring
    rw [sumNeg]
    simp only [actionCost]
    ring
  have negSupEqInf :
      -(Finset.univ.sup' Finset.univ_nonempty fun action =>
          -actionCost action) =
        Finset.univ.inf' Finset.univ_nonempty actionCost := by
    apply le_antisymm
    · apply Finset.le_inf' Finset.univ_nonempty
      intro action actionMem
      have bound := Finset.le_sup' (fun candidate => -actionCost candidate) actionMem
      linarith
    · obtain ⟨action, actionMem, actionMax⟩ :=
        Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun candidate => -actionCost candidate)
      calc
        Finset.univ.inf' Finset.univ_nonempty actionCost <= actionCost action :=
          Finset.inf'_le actionCost actionMem
        _ = -(Finset.univ.sup' Finset.univ_nonempty fun candidate =>
            -actionCost candidate) := by linarith
  change -(Finset.univ.sup' Finset.univ_nonempty fun action =>
    -loss state action + (gamma : Real) *
      Finset.univ.sum (fun nextState =>
        transition state action nextState * (-value nextState))) = _
  simpa only [actionNeg] using negSupEqInf
#print axioms discounted_loss_bellman_operator_apply

/-- At zero discount the policy operator is constant in the continuation value, so
pointwise greed alone identifies its fixed value; no transition-kernel premise is used. -/
theorem zero_discount_greedy_stationary_policy_is_optimal
    {State Action : Type*}
    [Fintype State] [TopologicalSpace State] [DiscreteTopology State]
    [Fintype Action] [Nonempty Action]
    (loss : State -> Action -> Real)
    (transition : State -> Action -> State -> Real)
    (policy : StationaryPolicy State Action)
    (optimalValue policyValue : State →ᵇ Real)
    (optimalFixed : Function.IsFixedPt
      (discountedLossBellmanOperator loss transition 0) optimalValue)
    (policyFixed : Function.IsFixedPt
      (stationaryPolicyBellmanOperator loss transition 0 policy) policyValue)
    (greedy : IsBellmanGreedy loss transition 0 policy optimalValue) :
    IsOptimalStationaryPolicy policy policyValue optimalValue := by
  have policyOperatorConstant :
      stationaryPolicyBellmanOperator loss transition 0 policy policyValue =
        stationaryPolicyBellmanOperator loss transition 0 policy optimalValue := by
    apply BoundedContinuousFunction.ext
    intro state
    simp [stationaryPolicyBellmanOperator, discountedLossBellmanOperator,
      discountedBellmanOperator]
  have optimalPolicyFixed : Function.IsFixedPt
      (stationaryPolicyBellmanOperator loss transition 0 policy) optimalValue := by
    apply BoundedContinuousFunction.ext
    intro state
    exact (greedy state).trans
      (congrArg (fun value : State →ᵇ Real => value state) optimalFixed)
  exact policyFixed.symm.trans (policyOperatorConstant.trans optimalPolicyFixed)
#print axioms zero_discount_greedy_stationary_policy_is_optimal

/-- In a finite-state ordinary MDP, any stationary policy that realizes the Bellman
minimum at every state has the same value function as the optimal fixed value. -/
theorem bellman_greedy_stationary_policy_is_optimal
    {State Action : Type*}
    [Fintype State] [TopologicalSpace State] [DiscreteTopology State]
    [Fintype Action] [Nonempty Action]
    (loss : State -> Action -> Real)
    (transition : State -> Action -> State -> Real)
    (gamma : NNReal) (hgamma_lt_one : gamma < 1)
    (htransition : IsStochasticTransition transition)
    (policy : StationaryPolicy State Action)
    (optimalValue policyValue : State →ᵇ Real)
    (optimalFixed : Function.IsFixedPt
      (discountedLossBellmanOperator loss transition gamma) optimalValue)
    (policyFixed : Function.IsFixedPt
      (stationaryPolicyBellmanOperator loss transition gamma policy) policyValue)
    (greedy : IsBellmanGreedy loss transition gamma policy optimalValue) :
    IsOptimalStationaryPolicy policy policyValue optimalValue := by
  classical
  rcases isEmpty_or_nonempty State with stateEmpty | stateNonempty
  · apply BoundedContinuousFunction.ext
    intro state
    exact isEmptyElim state
  letI : Nonempty State := stateNonempty
  by_cases hgamma_zero : gamma = 0
  · subst gamma
    exact zero_discount_greedy_stationary_policy_is_optimal loss transition policy
      optimalValue policyValue optimalFixed policyFixed greedy
  have hgamma_pos : 0 < gamma := pos_iff_ne_zero.mpr hgamma_zero
  have optimalPolicyFixed : Function.IsFixedPt
      (stationaryPolicyBellmanOperator loss transition gamma policy) optimalValue := by
    apply BoundedContinuousFunction.ext
    intro state
    exact (greedy state).trans
      (congrArg (fun value : State →ᵇ Real => value state) optimalFixed)
  let policyReward : State -> Unit -> Real :=
    fun state _ => -loss state (policy state)
  let policyTransition : State -> Unit -> State -> Real :=
    fun state _ nextState => transition state (policy state) nextState
  let rewardOperator : (State →ᵇ Real) -> State →ᵇ Real :=
    discountedBellmanOperator policyReward policyTransition gamma
  have rewardFixedOfPolicyFixed (value : State →ᵇ Real)
      (valueFixed : Function.IsFixedPt
        (stationaryPolicyBellmanOperator loss transition gamma policy) value) :
      Function.IsFixedPt rewardOperator (-value) := by
    change rewardOperator (-value) = -value
    have negated := congrArg Neg.neg valueFixed
    simpa only [stationaryPolicyBellmanOperator, discountedLossBellmanOperator,
      policyReward, policyTransition, rewardOperator, neg_neg] using negated
  rcases htransition with ⟨transitionNonnegative, transitionSum⟩
  have uniqueRewardFixed :=
    (discounted_bellman_contraction_and_unique_fixed_point
      policyReward policyTransition gamma hgamma_pos hgamma_lt_one
      (by
        intro state _ nextState
        exact transitionNonnegative state (policy state) nextState)
      (by
        intro state _
        exact transitionSum state (policy state))).2
  have negativeValuesEqual : -policyValue = -optimalValue :=
    uniqueRewardFixed.unique
      (rewardFixedOfPolicyFixed policyValue policyFixed)
      (rewardFixedOfPolicyFixed optimalValue optimalPolicyFixed)
  have valuesEqual := congrArg Neg.neg negativeValuesEqual
  simpa only [IsOptimalStationaryPolicy, neg_neg] using valuesEqual
#print axioms bellman_greedy_stationary_policy_is_optimal

/-- In a two-state self-loop MDP, a policy is greedy on every state reachable from
`false`, but is suboptimal at the unreachable state `true`. Thus initial-state
reachability is insufficient for global value-function optimality. -/
theorem reachable_only_greed_does_not_imply_global_optimality :
    let loss : Bool -> Bool -> Real :=
      fun state action => if action = state then 0 else 1
    let transition : Bool -> Bool -> Bool -> Real :=
      fun state _ nextState => if nextState = state then 1 else 0
    let policy : StationaryPolicy Bool Bool := fun _ => false
    let optimalValue : Bool →ᵇ Real := 0
    let policyValue : Bool →ᵇ Real :=
      BoundedContinuousFunction.mkOfCompact
        ⟨fun state => if state then 2 else 0, continuous_of_discreteTopology⟩
    IsStochasticTransition transition /\
      Function.IsFixedPt
        (discountedLossBellmanOperator loss transition (1 / 2)) optimalValue /\
      Function.IsFixedPt
        (stationaryPolicyBellmanOperator loss transition (1 / 2) policy) policyValue /\
      (forall state, PolicyReachable transition policy false state ->
        stationaryPolicyBellmanOperator loss transition (1 / 2) policy optimalValue state =
          discountedLossBellmanOperator loss transition (1 / 2) optimalValue state) /\
      ¬IsOptimalStationaryPolicy policy policyValue optimalValue := by
  dsimp only
  let policyValue : Bool →ᵇ Real :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun state => if state then 2 else 0, continuous_of_discreteTopology⟩
  have stochastic : IsStochasticTransition
      (fun state : Bool => fun _ : Bool => fun nextState : Bool =>
        if nextState = state then 1 else 0) := by
    constructor
    · intro state action nextState
      by_cases equality : nextState = state <;> simp [equality]
    · intro state action
      fin_cases state <;> simp
  have optimalFixed : Function.IsFixedPt
      (discountedLossBellmanOperator
        (fun state : Bool => fun action : Bool => if action = state then 0 else 1)
        (fun state : Bool => fun _ : Bool => fun nextState : Bool =>
          if nextState = state then 1 else 0) (1 / 2)) (0 : Bool →ᵇ Real) := by
    apply BoundedContinuousFunction.ext
    intro state
    rw [discounted_loss_bellman_operator_apply]
    fin_cases state <;> norm_num
  have policyFixed : Function.IsFixedPt
      (stationaryPolicyBellmanOperator
        (fun state : Bool => fun action : Bool => if action = state then 0 else 1)
        (fun state : Bool => fun _ : Bool => fun nextState : Bool =>
          if nextState = state then 1 else 0) (1 / 2) (fun _ => false)) policyValue := by
    apply BoundedContinuousFunction.ext
    intro state
    unfold stationaryPolicyBellmanOperator
    rw [discounted_loss_bellman_operator_apply]
    fin_cases state <;> norm_num [policyValue]
  refine ⟨stochastic, optimalFixed, policyFixed, ?_, ?_⟩
  · intro state reachable
    have stepEq {source target : Bool}
        (step : 0 < (if target = source then (1 : Real) else 0)) : target = source := by
      by_cases equality : target = source
      · exact equality
      · simp [equality] at step
    have stateEq : state = false := by
      induction reachable with
      | refl => rfl
      | tail path step ih =>
          exact (stepEq step).trans ih
    subst state
    unfold stationaryPolicyBellmanOperator
    rw [discounted_loss_bellman_operator_apply,
      discounted_loss_bellman_operator_apply]
    norm_num
  · intro valuesEqual
    change policyValue = (0 : Bool →ᵇ Real) at valuesEqual
    have atTrue := congrArg (fun value : Bool →ᵇ Real => value true) valuesEqual
    norm_num [IsOptimalStationaryPolicy, policyValue] at atTrue
#print axioms reachable_only_greed_does_not_imply_global_optimality

/-- The strict discount bound is load bearing for fixed-point value uniqueness: at
`gamma = 1`, a one-state zero-loss model has distinct fixed policy values. -/
theorem discount_factor_lt_one_is_necessary :
    let loss : Unit -> Unit -> Real := fun _ _ => 0
    let transition : Unit -> Unit -> Unit -> Real := fun _ _ _ => 1
    let policy : StationaryPolicy Unit Unit := fun _ => ()
    let zeroValue : Unit →ᵇ Real := 0
    let oneValue : Unit →ᵇ Real := 1
    IsStochasticTransition transition /\
      Function.IsFixedPt
        (discountedLossBellmanOperator loss transition 1) zeroValue /\
      Function.IsFixedPt
        (stationaryPolicyBellmanOperator loss transition 1 policy) oneValue /\
      IsBellmanGreedy loss transition 1 policy zeroValue /\
      ¬IsOptimalStationaryPolicy policy oneValue zeroValue := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> simp
  · apply BoundedContinuousFunction.ext
    intro state
    rw [discounted_loss_bellman_operator_apply]
    simp
  · apply BoundedContinuousFunction.ext
    intro state
    unfold stationaryPolicyBellmanOperator
    rw [discounted_loss_bellman_operator_apply]
    simp
  · intro state
    unfold stationaryPolicyBellmanOperator
    rw [discounted_loss_bellman_operator_apply]
  · intro valuesEqual
    change (1 : Unit →ᵇ Real) = 0 at valuesEqual
    have atUnit := congrArg (fun value : Unit →ᵇ Real => value ()) valuesEqual
    norm_num at atUnit
#print axioms discount_factor_lt_one_is_necessary

/-- On the empty state type all bounded value functions are extensionally equal, so
global policy optimality is vacuous and no nonemptiness assumption is needed. -/
theorem empty_state_policy_values_equal {Action : Type*}
    (policy : StationaryPolicy Empty Action)
    (policyValue optimalValue : Empty →ᵇ Real) :
    IsOptimalStationaryPolicy policy policyValue optimalValue := by
  apply BoundedContinuousFunction.ext
  intro state
  exact isEmptyElim state
#print axioms empty_state_policy_values_equal

/-- With one available action every stationary policy is automatically Bellman-greedy. -/
theorem singleton_action_policy_is_automatically_greedy
    {State : Type*}
    [Fintype State] [TopologicalSpace State] [DiscreteTopology State]
    (loss : State -> Unit -> Real)
    (transition : State -> Unit -> State -> Real)
    (gamma : NNReal) (value : State →ᵇ Real) :
    IsBellmanGreedy loss transition gamma (fun _ => ()) value := by
  intro state
  unfold stationaryPolicyBellmanOperator
  rw [discounted_loss_bellman_operator_apply]
#print axioms singleton_action_policy_is_automatically_greedy

/-- In the one-state self-loop model with constant loss three and half discount,
every policy is greedy and both its policy value and the optimal value are six. -/
theorem constant_loss_single_state_all_policies_are_optimal
    (policy : StationaryPolicy Unit Bool) :
    let loss : Unit -> Bool -> Real := fun _ _ => 3
    let transition : Unit -> Bool -> Unit -> Real := fun _ _ _ => 1
    let value : Unit →ᵇ Real := 6
    IsStochasticTransition transition /\
      Function.IsFixedPt
        (discountedLossBellmanOperator loss transition (1 / 2)) value /\
      Function.IsFixedPt
        (stationaryPolicyBellmanOperator loss transition (1 / 2) policy) value /\
      IsBellmanGreedy loss transition (1 / 2) policy value /\
      IsOptimalStationaryPolicy policy value value := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · constructor <;> simp
  · apply BoundedContinuousFunction.ext
    intro state
    rw [discounted_loss_bellman_operator_apply]
    norm_num
  · apply BoundedContinuousFunction.ext
    intro state
    rw [stationaryPolicyBellmanOperator, discounted_loss_bellman_operator_apply]
    norm_num
  · intro state
    rw [stationaryPolicyBellmanOperator, discounted_loss_bellman_operator_apply,
      discounted_loss_bellman_operator_apply]
    norm_num
#print axioms constant_loss_single_state_all_policies_are_optimal

end D5.S3.Observer.DynamicProgramming.StationaryPolicyOptimality
