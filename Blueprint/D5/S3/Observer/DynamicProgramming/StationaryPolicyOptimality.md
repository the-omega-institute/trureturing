# Stationary Policy Optimality

## Abstract

Bellman-greedy stationary policies have the optimal discounted value, with sharp global-state and discount hypotheses.

**Theorem 1.1 (The loss Bellman operator is a finite minimum).**

$$\operatorname{LossBellman}\left(ell, P, \gamma, v, s\right) = \operatorname{inf}_{a\in A} (ell\left(s, a\right) + \gamma \sum_{t\in S} P\left(s, a, t\right) \times v\left(t\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.discounted_loss_bellman_operator_apply` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sign conjugation turns the existing finite reward maximum into immediate loss plus discounted continuation, minimized over the finite action set.

**Theorem 1.2 (Greed remains sufficient at zero discount).**

$$\gamma = 0 \land \operatorname{Fixed}\left(T, V^{*}\right) \land \operatorname{Fixed}\left(Tpi, V^{pi}\right) \land \operatorname{GreedyEverywhere}\left(pi, V^{*}\right) \Rightarrow V^{pi} = V^{*}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.zero_discount_greedy_stationary_policy_is_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero discount the continuation value disappears. The policy operator is constant, so its fixed value equals the greedy optimal fixed value without any stochastic-kernel premise.

**Theorem 1.3 (Everywhere Bellman-greedy stationary policies are optimal).**

$$0 \leq \gamma < 1 \land \operatorname{Stochastic}\left(P\right) \land \operatorname{Fixed}\left(T, V^{*}\right) \land \operatorname{Fixed}\left(Tpi, V^{pi}\right) \land \operatorname{GreedyEverywhere}\left(pi, V^{*}\right) \Rightarrow V^{pi} = V^{*}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.bellman_greedy_stationary_policy_is_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is a finite-state ordinary-MDP formalization, not a belief-simplex formalization. The policy selects an action at every state and realizes the Bellman loss minimum there.

Greed makes the optimal value a fixed point of the fixed-policy operator. The existing discounted Bellman contraction theorem, instantiated with the singleton chosen action, makes that fixed point unique. Hence the policy value equals the optimal value.

**Theorem 1.4 (Reachable-only greed is not global optimality).**

$$\operatorname{ReachableFrom}\left(pi, false\right) = \{false\} \land \operatorname{GreedyOnReachable}\left(pi, false\right) \land \operatorname{PolicyValue}\left(pi, true\right) = 2 \land \operatorname{OptimalValue}\left(true\right) = 0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.reachable_only_greed_does_not_imply_global_optimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two self-loop states make true unreachable from the initial false state. The policy is greedy at false but incurs value two at true, whereas the globally optimal value is zero.

**Theorem 1.5 (The strict discount bound is necessary).**

$$\gamma = 1 \land \operatorname{Fixed}\left(Tpi, 0\right) \land \operatorname{Fixed}\left(Tpi, 1\right) \land 0 \neq 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.discount_factor_lt_one_is_necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At discount one, the one-state zero-loss self-loop policy operator is the identity and therefore fixes both zero and one. Fixed-point value uniqueness, and thus this proof of policy optimality, fails.

**Theorem 1.6 (Empty-state policy optimality is vacuous).**

$$\operatorname{Empty}\left(S\right) \Rightarrow \forall V^{pi}, V^{*}, V^{pi} = V^{*}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.empty_state_policy_values_equal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every two bounded functions on the empty state type are extensionally equal, so no state nonemptiness assumption belongs in the policy optimality conclusion.

**Theorem 1.7 (A singleton action set makes greed automatic).**

$$A = \{a\} \Rightarrow \forall pi, \operatorname{GreedyEverywhere}\left(pi, v\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.singleton_action_policy_is_automatically_greedy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With one action, the policy operator and the action-minimizing Bellman operator are definitionally the same finite minimum.

**Theorem 1.8 (Constant loss makes every policy optimal in the singleton model).**

$$S = \{s\} \land ell = 3 \land \gamma = \frac{1}{2} \Rightarrow \forall pi, \operatorname{PolicyValue}\left(pi\right) = \operatorname{OptimalValue}\left(\right) = 6.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.constant_loss_single_state_all_policies_are_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one self-loop state, constant loss three, and half discount, every action has the same Bellman value six. Thus every policy is greedy and has the same value; the greed condition is automatic, not false.

## References

- Truth anchor: `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.bellman_greedy_stationary_policy_is_optimal`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.constant_loss_single_state_all_policies_are_optimal`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.discount_factor_lt_one_is_necessary`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.discounted_loss_bellman_operator_apply`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.empty_state_policy_values_equal`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.reachable_only_greed_does_not_imply_global_optimality`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.singleton_action_policy_is_automatically_greedy`
- Truth anchor: `D5/S3/Observer/DynamicProgramming/StationaryPolicyOptimality.zero_discount_greedy_stationary_policy_is_optimal`
- Dependency: [D5/S3/Observer/DynamicProgramming/DiscountedBellmanContraction](DiscountedBellmanContraction.md)
