# Three-State Adaptive Early Stopping

## Abstract

A three-state early-stopping tree preserves exact identification and lowers expected experiment cost.

**Theorem 1.1 (Adaptive early stopping has a strict expected-cost advantage).**

$$\forall epsilon \in Real,\; \left(0 < epsilon \land epsilon < \frac{1}{2}\right) \Rightarrow \begin{gathered}\operatorname{let} X := Option\left(Bool\right),\\{}pi\left(none\right) = 1 - 2epsilon, pi\left(some\left(false\right)\right) = pi\left(some\left(true\right)\right) = epsilon,\\{}A\left(none\right) = true, A\left(some\left(false\right)\right) = A\left(some\left(true\right)\right) = false,\\{}B\left(some\left(true\right)\right) = true, B\left(none\right) = B\left(some\left(false\right)\right) = false,\\{}S\left(x\right) := [A\left(x\right), B\left(x\right)],\\{}T\left(x\right) := ite\left(A\left(x\right), [true], [false, B\left(x\right)]\right),\\{}\left(\left(\forall x \in X,\; 0 \leq pi\left(x\right)\right) \land \sum_{x \in X} pi\left(x\right) = 1\right) \land \left(Injective\left(S\right) \land \left(Injective\left(T\right) \land \left(\left(\left(\forall x \in X,\; length\left(T\left(x\right)\right) \leq 2\right) \land \left(\exists x \in X,\; length\left(T\left(x\right)\right) = 2\right)\right) \land \left(\sum_{x \in X} pi\left(x\right) \cdot length\left(S\left(x\right)\right) = 2 \land \left(\sum_{x \in X} pi\left(x\right) \cdot length\left(T\left(x\right)\right) = 1 + 2epsilon \land \sum_{x \in X} pi\left(x\right) \cdot length\left(T\left(x\right)\right) < \sum_{x \in X} pi\left(x\right) \cdot length\left(S\left(x\right)\right)\right)\right)\right)\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping.three_state_adaptive_early_stopping_strict_advantage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state encoding is a three-point option type. The distinguished none state has mass one minus twice epsilon, and each remaining state has mass epsilon.

The fixed transcript always reads both deterministic experiments. The adaptive transcript stops after the first answer exactly on the distinguished state.

Injectivity states zero-error identification. The length clauses give worst-case cost two, static mean two, and adaptive mean one plus twice epsilon.

## References

- Truth anchor: `D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping.three_state_adaptive_early_stopping_strict_advantage`
- Dependency: [D5/S3/ConceptDynamics/Experiment/PosteriorInformationGainIncrease](../Experiment/PosteriorInformationGainIncrease.md)
