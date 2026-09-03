# Testing Cost Classification

## Abstract

Testing-name code length filters, table execution cost does not, and mixed cost filters.

**Lemma 1.1 (A fixed-support-size execution sublevel is infinite).**

$$\forall O: \operatorname{Type}, \forall o0: O,\\{}\forall programCost: \mathbb{N} \to \mathbb{N}, \operatorname{Infinite}\left(\left\{\operatorname{testingExecutionCost}\left(programCost, a\right) \leq 1 \mid a \in \operatorname{TestingName}\left(O\right)\right\}\right).$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/TestingCostClassification.fixed_support_execution_sublevel_infinite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Singleton supports embed the natural numbers into distinct finite-table names. Every such table has execution cost one, so execution cost alone cannot supply finite sublevels.

**Theorem 1.2 (Testing-name cost classification).**

$$\begin{gathered}\forall O: \operatorname{Type}, \forall o0: O,\\{}\forall code: \operatorname{TestingName}\left(O\right) \to \operatorname{List}\left(Bool\right), \forall programCost: \mathbb{N} \to \mathbb{N},\\{}\operatorname{Injective}\left(code\right) \Rightarrow ((\forall Q: \mathbb{N}, \operatorname{Finite}\left(\left\{\operatorname{length}\left(\operatorname{code}\left(a\right)\right) \leq Q \mid a \in \operatorname{TestingName}\left(O\right)\right\}\right)) \land\\{}\operatorname{Infinite}\left(\left\{\operatorname{testingExecutionCost}\left(programCost, a\right) \leq 1 \mid a \in \operatorname{TestingName}\left(O\right)\right\}\right) \land\\{}(\forall Q: \mathbb{N}, \operatorname{Finite}\left(\left\{\operatorname{length}\left(\operatorname{code}\left(a\right)\right) + \operatorname{natLog}\left(2, \operatorname{testingExecutionCost}\left(programCost, a\right)\right) \leq Q \mid a \in \operatorname{TestingName}\left(O\right)\right\}\right))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/TestingCostClassification.testing_cost_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first clause applies the frozen testing-name code-length owner to an injective self-delimiting Boolean code.

The second clause is the singleton-support counterfamily. The third observes that every mixed-cost sublevel lies inside the corresponding finite code-length sublevel.

## References

- Truth anchor: `D5/S0/Naming/TestingCostClassification.fixed_support_execution_sublevel_infinite`
- Truth anchor: `D5/S0/Naming/TestingCostClassification.testing_cost_classification`
- Dependency: [D5/S0/Naming/Conservation/TestingTowerMembership](Conservation/TestingTowerMembership.md)
