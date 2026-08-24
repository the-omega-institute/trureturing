/- GID: D5/S3/Observer/DynamicProgramming/DiscountedBellmanContraction
   generality: G
   mirror-B: D5/B/S3/Observer/DynamicProgramming/DiscountedBellmanContraction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite-state finite-action discounted Bellman operator is a strict sup-norm contraction and therefore has a unique fixed value function. -/

import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'discounted_bellman_contraction_and_unique_fixed_point' D5
     Golden/Frozen/accepted` returned no match before this module was created.
   * Public repository hits `bellman_operator_contracting_unique_fixed_point` and
     `bellman_contraction_unique_fixed_point_and_iteration_bound` respectively concern a
     deterministic pairwise maximum and assume the active operator's Lipschitz estimate;
     neither proves contraction for normalized transition probabilities and action maxima.
   * No private Bellman contraction theorem was found. Pinned Mathlib supplies
     `Finset.sup'_le`, `Finset.le_sup'`, `ContractingWith.fixedPoint_isFixedPt`, and
     `ContractingWith.fixedPoint_unique`; `ContractingWith.exists_fixedPoint` underlies that
     Banach API. `BoundedContinuousFunction.instCompleteSpace` and `norm_le_of_nonempty`
     provide the complete uniform-norm value space. The finite-sup lemmas control actions.
     `command -v loogle` and `command -v leansearch` both returned no executable. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.DynamicProgramming.DiscountedBellmanContraction

open scoped BigOperators BoundedContinuousFunction

/-- The finite-action Bellman optimality operator with discounted expected continuation. -/
noncomputable def discountedBellmanOperator {State Action : Type*}
    [Fintype State] [TopologicalSpace State] [DiscreteTopology State]
    [Fintype Action] [Nonempty Action]
    (reward : State -> Action -> Real)
    (transition : State -> Action -> State -> Real)
    (gamma : NNReal) (value : State →ᵇ Real) : State →ᵇ Real :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun state =>
        Finset.univ.sup' Finset.univ_nonempty fun action =>
          reward state action +
            (gamma : Real) *
              ∑ nextState : State, transition state action nextState * value nextState,
      continuous_of_discreteTopology⟩

/-- For finite states and actions, nonnegative normalized transition weights make the
discounted Bellman operator a `gamma` contraction in the uniform norm. Banach's theorem
then gives its unique fixed value function. -/
theorem discounted_bellman_contraction_and_unique_fixed_point
    {State Action : Type*}
    [Fintype State] [Nonempty State] [TopologicalSpace State] [DiscreteTopology State]
    [Fintype Action] [Nonempty Action]
    (reward : State -> Action -> Real)
    (transition : State -> Action -> State -> Real)
    (gamma : NNReal) (hgamma_pos : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (htransition_nonnegative :
      ∀ state action nextState, 0 ≤ transition state action nextState)
    (htransition_sum : ∀ state action, ∑ nextState, transition state action nextState = 1) :
    (∀ value other : State →ᵇ Real,
        ‖discountedBellmanOperator reward transition gamma value -
            discountedBellmanOperator reward transition gamma other‖ ≤
          (gamma : Real) * ‖value - other‖) ∧
      ∃! value : State →ᵇ Real,
        Function.IsFixedPt (discountedBellmanOperator reward transition gamma) value := by
  let actionValue : (State →ᵇ Real) -> State -> Action -> Real :=
    fun value state action =>
      reward state action +
        (gamma : Real) *
          ∑ nextState : State, transition state action nextState * value nextState
  have hgamma_nonnegative : 0 ≤ (gamma : Real) := by
    exact_mod_cast hgamma_pos.le
  have expectation_bound (value other : State →ᵇ Real) (state : State) (action : Action) :
      |(∑ nextState : State, transition state action nextState * value nextState) -
          ∑ nextState : State, transition state action nextState * other nextState| ≤
        ‖value - other‖ := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ nextState : State,
          (transition state action nextState * value nextState -
            transition state action nextState * other nextState)| =
          |∑ nextState : State,
            transition state action nextState * (value nextState - other nextState)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro nextState _
        ring
      _ ≤ ∑ nextState : State,
          |transition state action nextState * (value nextState - other nextState)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ nextState : State,
          transition state action nextState * |value nextState - other nextState| := by
        apply Finset.sum_congr rfl
        intro nextState _
        rw [abs_mul, abs_of_nonneg (htransition_nonnegative state action nextState)]
      _ ≤ ∑ nextState : State, transition state action nextState * ‖value - other‖ := by
        apply Finset.sum_le_sum
        intro nextState _
        apply mul_le_mul_of_nonneg_left _
          (htransition_nonnegative state action nextState)
        simpa only [BoundedContinuousFunction.coe_sub, Pi.sub_apply, Real.norm_eq_abs] using
          BoundedContinuousFunction.norm_coe_le_norm (value - other) nextState
      _ = ‖value - other‖ := by
        rw [← Finset.sum_mul, htransition_sum state action, one_mul]
  have action_bound (value other : State →ᵇ Real) (state : State) (action : Action) :
      |actionValue value state action - actionValue other state action| ≤
        (gamma : Real) * ‖value - other‖ := by
    simp only [actionValue]
    calc
      |(reward state action +
            (gamma : Real) *
              ∑ nextState : State, transition state action nextState * value nextState) -
          (reward state action +
            (gamma : Real) *
              ∑ nextState : State, transition state action nextState * other nextState)| =
          (gamma : Real) *
            |(∑ nextState : State, transition state action nextState * value nextState) -
              ∑ nextState : State,
                transition state action nextState * other nextState| := by
        rw [show
          (reward state action +
              (gamma : Real) *
                ∑ nextState : State, transition state action nextState * value nextState) -
            (reward state action +
              (gamma : Real) *
                ∑ nextState : State,
                  transition state action nextState * other nextState) =
            (gamma : Real) *
              ((∑ nextState : State,
                  transition state action nextState * value nextState) -
                ∑ nextState : State,
                  transition state action nextState * other nextState) by ring]
        rw [abs_mul, abs_of_nonneg hgamma_nonnegative]
      _ ≤ (gamma : Real) * ‖value - other‖ :=
        mul_le_mul_of_nonneg_left (expectation_bound value other state action)
          hgamma_nonnegative
  have pointwise_bound (value other : State →ᵇ Real) (state : State) :
      |discountedBellmanOperator reward transition gamma value state -
          discountedBellmanOperator reward transition gamma other state| ≤
        (gamma : Real) * ‖value - other‖ := by
    change
      |Finset.univ.sup' Finset.univ_nonempty (actionValue value state) -
          Finset.univ.sup' Finset.univ_nonempty (actionValue other state)| ≤
        (gamma : Real) * ‖value - other‖
    have forward :
        Finset.univ.sup' Finset.univ_nonempty (actionValue value state) ≤
          Finset.univ.sup' Finset.univ_nonempty (actionValue other state) +
            (gamma : Real) * ‖value - other‖ := by
      refine Finset.sup'_le Finset.univ_nonempty _ ?_
      intro action _
      calc
        actionValue value state action ≤
            actionValue other state action + (gamma : Real) * ‖value - other‖ := by
          have bound := action_bound value other state action
          rw [abs_le] at bound
          linarith
        _ ≤ Finset.univ.sup' Finset.univ_nonempty (actionValue other state) +
            (gamma : Real) * ‖value - other‖ := by
          exact add_le_add
            (Finset.le_sup' (actionValue other state) (Finset.mem_univ action)) le_rfl
    have backward :
        Finset.univ.sup' Finset.univ_nonempty (actionValue other state) ≤
          Finset.univ.sup' Finset.univ_nonempty (actionValue value state) +
            (gamma : Real) * ‖value - other‖ := by
      refine Finset.sup'_le Finset.univ_nonempty _ ?_
      intro action _
      calc
        actionValue other state action ≤
            actionValue value state action + (gamma : Real) * ‖value - other‖ := by
          have bound := action_bound value other state action
          rw [abs_le] at bound
          linarith
        _ ≤ Finset.univ.sup' Finset.univ_nonempty (actionValue value state) +
            (gamma : Real) * ‖value - other‖ := by
          exact add_le_add
            (Finset.le_sup' (actionValue value state) (Finset.mem_univ action)) le_rfl
    rw [abs_le]
    constructor <;> linarith
  have norm_bound (value other : State →ᵇ Real) :
      ‖discountedBellmanOperator reward transition gamma value -
          discountedBellmanOperator reward transition gamma other‖ ≤
        (gamma : Real) * ‖value - other‖ := by
    apply BoundedContinuousFunction.norm_le_of_nonempty.2
    intro state
    simpa only [BoundedContinuousFunction.coe_sub, Pi.sub_apply, Real.norm_eq_abs] using
      pointwise_bound value other state
  let operator := discountedBellmanOperator reward transition gamma
  have contracting : ContractingWith gamma operator := by
    refine ⟨hgamma_lt_one, LipschitzWith.of_dist_le_mul ?_⟩
    intro value other
    simpa only [operator, dist_eq_norm] using norm_bound value other
  refine ⟨norm_bound, ?_⟩
  let fixedValue := ContractingWith.fixedPoint operator contracting
  have fixedValue_fixed : Function.IsFixedPt operator fixedValue :=
    contracting.fixedPoint_isFixedPt
  refine ⟨fixedValue, ?_, ?_⟩
  · simpa only [operator] using fixedValue_fixed
  · intro candidate candidate_fixed
    apply contracting.fixedPoint_unique
    simpa only [operator] using candidate_fixed

example :
    ∃! value : Unit →ᵇ Real,
      Function.IsFixedPt
        (discountedBellmanOperator
          (fun _ : Unit => fun _ : Unit => 0)
          (fun _ : Unit => fun _ : Unit => fun _ : Unit => 1) (1 / 2)) value := by
  have result :=
    discounted_bellman_contraction_and_unique_fixed_point
      (State := Unit) (Action := Unit)
      (fun _ _ => 0) (fun _ _ _ => 1) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by simp)
  exact result.2

#print axioms discounted_bellman_contraction_and_unique_fixed_point

end D5.S3.Observer.DynamicProgramming.DiscountedBellmanContraction
