# Optimal Binary Answer with Abstention

## Abstract

Binary posterior loss selects answer zero, abstention, or answer one at the stated thresholds.

**Theorem 1.1 (Optimal choice).**

$$\begin{gathered}\forall p\in [0, 1], 0 < \lambda < \frac{1}{2},\\{}a^{*}(p, \lambda) = \begin{cases}\text{answer\ 0},&p \leq \lambda\\{}\text{abstain},&\lambda < p < 1 - \lambda\\{}\text{answer\ 1},&p \geq 1 - \lambda\end{cases}.\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DecisionValue/OptimalBinaryAbstention.optimal_binary_answer_with_abstention` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The binary target has posterior probability p of value one. Answering zero has expected loss p, abstaining has loss lambda, and answering one has expected loss 1-p.

The selector is constructed by comparing those three losses, with the source's endpoint preference. Linear comparison yields answer zero below the lower threshold, abstention strictly between the thresholds, and answer one at and above the upper threshold.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DecisionValue/OptimalBinaryAbstention.optimal_binary_answer_with_abstention`
