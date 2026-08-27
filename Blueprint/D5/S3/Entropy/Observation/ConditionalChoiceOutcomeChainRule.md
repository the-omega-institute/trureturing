# Conditional Choice-Outcome Chain Rule

## Abstract

Conditional entropy separates a choice from its subsequent outcome.

**Theorem 1.1 (Choice-outcome conditional entropy obeys the chain rule).**

$$\forall Q \in Type, A \in Type, Y \in Type, p \in Q \times A \times Y \to \mathbb{R},\; Fintype\left(Q\right) \land Fintype\left(A\right) \land Fintype\left(Y\right) \land \forall z: Q \times A \times Y, 0 \leq p\left(z\right) \Rightarrow H(A \times Y \mid Q) = H(A \mid Q) + H(Y \mid Q \times A)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/ConditionalChoiceOutcomeChainRule.conditional_choice_outcome_chain_rule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite joint mass is carried directly on public context, choice, and outcome. Its context-choice marginal is the canonical xyProjection.

The first summand measures the choice left undecided by the public context; the second measures the outcome left undecided after both context and choice are supplied.

## References

- Truth anchor: `D5/S3/Entropy/Observation/ConditionalChoiceOutcomeChainRule.conditional_choice_outcome_chain_rule`
- Dependency: [D5/S3/Entropy/Submodularity/StrongSubadditivity](../Submodularity/StrongSubadditivity.md)
