# Finite-Precision Runtime Reduction

## Abstract

A fixed finite-precision runtime is a finite deterministic observation system.

**Theorem 1.1 (Finite-precision runtime reduction).**

$$\forall C, K, R, M, S, O, Theta, External: \operatorname{Type},\ [\operatorname{Fintype}(C)], [\operatorname{Fintype}(K)], [\operatorname{Fintype}(R)], [\operatorname{Fintype}(M)], [\operatorname{Fintype}(S)], [\operatorname{Fintype}(O)], [\operatorname{Fintype}(Theta)], [\operatorname{IsEmpty}(External)],\ theta: Theta, update: Theta \to \operatorname{RuntimeState}(C, K, R, M, S) \to \operatorname{RuntimeState}(C, K, R, M, S), readout: Theta \to \operatorname{RuntimeState}(C, K, R, M, S) \to O,\ N b: \mathbb{N}, parameterEncoding: Theta \to \operatorname{ParameterSlots}(N, b), hParameterInjective: \operatorname{Injective}(parameterEncoding), onlineLearning: Prop,\ \exists system: \operatorname{ObservationSystem}(\operatorname{RuntimeState}(C, K, R, M, S), O), \operatorname{transition}(system) = update(theta) \land \operatorname{readout}(system) = readout(theta) \land \operatorname{card}(\operatorname{RuntimeState}(C, K, R, M, S)) = \operatorname{card}(C) \times \operatorname{card}(K) \times \operatorname{card}(R) \times \operatorname{card}(M) \times \operatorname{card}(S) \land \operatorname{card}(Theta) \leq 2^{b \times N} \land (onlineLearning \Rightarrow \forall Optimizer: \operatorname{Type} [\operatorname{Fintype}(Optimizer)], \operatorname{card}(\operatorname{Prod}(\operatorname{Prod}(\operatorname{RuntimeState}(C, K, R, M, S), Theta), Optimizer)) = \operatorname{card}(\operatorname{RuntimeState}(C, K, R, M, S)) \times \operatorname{card}(Theta) \times \operatorname{card}(Optimizer)).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/FiniteRuntimeReduction.finite_precision_runtime_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete runtime state is constructed as the product of the five finite source components C, K, R, M, and S. Fixed parameters make the update and readout deterministic maps on that product, while the empty external-input type records the absence of uncounted inputs.

The public conclusion includes the exact product cardinality, an injective b-bit encoding bound for N parameter slots, and the expanded product cardinality when online learning carries parameters and optimizer state.

Repository search found no packaged theorem with this complete reduction. Pinned Mathlib supplies and is applied through Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, and Fintype.card_le_of_injective.

## References

- Truth anchor: `D5/S3/QuantumStates/FiniteRuntimeReduction.finite_precision_runtime_reduction`
