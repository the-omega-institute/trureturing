# Blackwell Order and External Cost

## Abstract

Blackwell dominance orders decision information but imposes no order on an independently assigned nonnegative implementation cost.

**Theorem 1.1 (Blackwell dominance can have higher cost).**

$$\exists P, Q: \operatorname{Kernel}\left(Bool, Bool\right), cost: \operatorname{ExperimentCost}\left(Bool, Bool\right),\\{}P \neq Q \land \operatorname{BlackwellDominates}\left(P, Q\right) \land cost\left(P\right) > cost\left(Q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.exists_blackwell_dominance_with_higher_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Implementation cost is a named function from experiment kernels to nonnegative reals, with no compatibility axiom connecting it to Blackwell dominance.

The Boolean identity experiment Blackwell-dominates the constant erasure experiment. They are distinct, and assigning costs one and zero respectively gives the strict higher-cost direction.

**Theorem 1.2 (Blackwell dominance can have lower cost).**

$$\exists P, Q: \operatorname{Kernel}\left(Bool, Bool\right), cost: \operatorname{ExperimentCost}\left(Bool, Bool\right),\\{}P \neq Q \land \operatorname{BlackwellDominates}\left(P, Q\right) \land cost\left(P\right) < cost\left(Q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.exists_blackwell_dominance_with_lower_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same distinct Boolean experiment pair, reversing the two assigned costs makes the dominating experiment strictly cheaper.

Together with the higher-cost witness, this shows that Blackwell dominance alone determines neither strict cost direction.

**Theorem 1.3 (Equal experiments have equal cost).**

$$\forall \theta, X, cost: \operatorname{ExperimentCost}\left(\theta, X\right),\\{}P, Q: \operatorname{Kernel}\left(\theta, X\right), P = Q \Rightarrow cost\left(P\right) = cost\left(Q\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.equal_experiments_have_equal_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Because an external cost assignment is still a function, equal kernels must receive equal values by congruence.

Thus reflexive Blackwell dominance is not itself a strict-cost witness; the two existence theorems deliberately use distinct identity and erasure kernels.

**Theorem 1.4 (Constant cost cannot strictly compare experiments).**

$$\forall \theta, X, c: \mathbb{R}_{\geq 0}, P, Q: \operatorname{Kernel}\left(\theta, X\right),\\{}\neg{\operatorname{constCost}\left(c\right)\left(P\right) > \operatorname{constCost}\left(c\right)\left(Q\right)} \land \neg{\operatorname{constCost}\left(c\right)\left(P\right) < \operatorname{constCost}\left(c\right)\left(Q\right)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.constant_experiment_cost_cannot_strictly_compare` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A constant assignment gives the same nonnegative value to every kernel, so neither strict comparison can hold for any pair.

Accordingly the concrete existence witnesses use nonconstant cost functions; their strict inequalities carry that requirement.

**Theorem 1.5 (Constant Boolean experiments are Blackwell-equivalent).**

$$\operatorname{BlackwellDominates}\left(K_{0}, K_{1}\right) \land \operatorname{BlackwellDominates}\left(K_{1}, K_{0}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.constant_boolean_experiments_are_blackwell_equivalent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The always-false and always-true Boolean experiments can each be obtained from the other by constant deterministic processing.

This verifies the fully uninformative degenerate case directly and shows that mutual dominance supplies no external cost order.

**Theorem 1.6 (Blackwell dominance still compares Bayes risk).**

$$\begin{gathered}\forall P: \operatorname{Kernel}\left(\theta, X\right), Q: \operatorname{Kernel}\left(\theta, X_{1}\right),\\{}\operatorname{BlackwellDominates}\left(P, Q\right) \Rightarrow\\{}\forall \ell: \theta \to Y \to ENNReal, \pi: \operatorname{Measure}\left(\theta\right),\\{}\operatorname{bayesRisk}\left(\ell, P, \pi\right) \leq \operatorname{bayesRisk}\left(\ell, Q, \pi\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.blackwell_dominance_still_compares_bayes_risk` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every extended-nonnegative loss and prior measure, a dominating experiment has no larger optimal Bayes risk.

This is a direct application of the established Blackwell theorem. Only the unrelated external cost comparison is unconstrained.

## References

- Truth anchor: `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.blackwell_dominance_still_compares_bayes_risk`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.constant_boolean_experiments_are_blackwell_equivalent`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.constant_experiment_cost_cannot_strictly_compare`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.equal_experiments_have_equal_cost`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.exists_blackwell_dominance_with_higher_cost`
- Truth anchor: `D5/S3/Estimation/ExperimentCost/BlackwellCostOrthogonality.exists_blackwell_dominance_with_lower_cost`
- Dependency: [D5/S3/Estimation/DecisionRisk/GarblingIncreasesBayesRisk](../DecisionRisk/GarblingIncreasesBayesRisk.md)
