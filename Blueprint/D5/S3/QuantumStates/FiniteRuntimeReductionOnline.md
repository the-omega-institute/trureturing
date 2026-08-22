# Finite Runtime Reduction with Online State Extension

## Abstract

A fixed finite-precision runtime is finite, and online learning requires an expanded state.

**Theorem 1.1 (Finite-precision runtime reduction with online state extension).**

$$\forall C, K, R, M, S, O, Theta, Optimizer: \operatorname{Type},\ [\operatorname{Fintype}(C)], [\operatorname{Fintype}(K)], [\operatorname{Fintype}(R)], [\operatorname{Fintype}(M)], [\operatorname{Fintype}(S)], [\operatorname{Finite}(O)], [\operatorname{Fintype}(Theta)], [\operatorname{Fintype}(Optimizer)],\ theta: Theta, update: Theta \to \operatorname{RuntimeState}(C, K, R, M, S) \to \operatorname{RuntimeState}(C, K, R, M, S), readout: Theta \to \operatorname{RuntimeState}(C, K, R, M, S) \to O,\ N b: \mathbb{N}, parameterEncoding: Theta \to \operatorname{ParameterSlots}(N, b), hParameterInjective: \operatorname{Injective}(parameterEncoding), onlineUpdate: \operatorname{LearningState}(C, K, R, M, S, Theta, Optimizer) \to \operatorname{LearningState}(C, K, R, M, S, Theta, Optimizer), onlineReadout: \operatorname{LearningState}(C, K, R, M, S, Theta, Optimizer) \to O,\ \exists system: \operatorname{ObservationSystem}(\operatorname{RuntimeState}(C, K, R, M, S), O), \operatorname{transition}(system) = \operatorname{Apply}(update, theta) \land \operatorname{readout}(system) = \operatorname{Apply}(readout, theta) \land \operatorname{card}(\operatorname{RuntimeState}(C, K, R, M, S)) = \operatorname{card}(C) \times \operatorname{card}(K) \times \operatorname{card}(R) \times \operatorname{card}(M) \times \operatorname{card}(S) \land \operatorname{card}(Theta) \leq 2^{b \times N} \land (\operatorname{onlineLearningOccurred}(onlineUpdate, onlineReadout) \Rightarrow ((\exists onlineSystem: \operatorname{ObservationSystem}(\operatorname{LearningState}(C, K, R, M, S, Theta, Optimizer), O), \operatorname{transition}(onlineSystem) = onlineUpdate \land \operatorname{readout}(onlineSystem) = onlineReadout \land \operatorname{card}(\operatorname{LearningState}(C, K, R, M, S, Theta, Optimizer)) = \operatorname{card}(\operatorname{RuntimeState}(C, K, R, M, S)) \times \operatorname{card}(Theta) \times \operatorname{card}(Optimizer) \land \exists state, (onlineUpdate(state).2.1 \neq state.2.1 \lor onlineUpdate(state).2.2 \neq state.2.2)) \land \neg \exists fixedReadout: \operatorname{RuntimeState}(C, K, R, M, S) \to O, \forall state, fixedReadout(state.1) = onlineReadout(state))).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumStates/FiniteRuntimeReductionOnline.finite_precision_runtime_reduction_online` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete runtime state is constructed as the product of the five finite source components C, K, R, M, and S. Fixed parameters make the update and readout deterministic maps on that product; no uncounted input appears in either function's domain.

The public conclusion includes the exact product cardinality and the injective b-bit parameter bound. Its online clause constructs the expanded runtime state, records an actual parameter or optimizer mutation, and rules out collapse to a fixed runtime when that mutation changes the readout against frozen old values.

Repository search found no exact packaged theorem. Pinned Mathlib supplies and is applied through Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, and Fintype.card_le_of_injective.

## References

- Truth anchor: `D5/S3/QuantumStates/FiniteRuntimeReductionOnline.finite_precision_runtime_reduction_online`
