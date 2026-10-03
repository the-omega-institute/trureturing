# Controlled Observable Completion

## Abstract

Finite nonnegative Hamiltonian control words have a sharp observable completion.

**Theorem 1.1 (Controlled observations and minimal expectation coordinates).**

$$\exists k \leq m^{2} - \operatorname{dim}(W_{0}), W_{k} = W_{k + 1} = W,\\{}\operatorname{PredictEq}(\rho, sigma) \iff \forall O \in W, \operatorname{Tr}((\rho - sigma)O) = 0,\\{}\operatorname{SufficientPhysical}(S) := \forall \rho, sigma \in Density, \operatorname{S}(\rho) = \operatorname{S}(sigma) \Rightarrow \forall word \in LegalWords, \forall b, \operatorname{Tr}(\rho \operatorname{wordReadout}(word, b)) = \operatorname{Tr}(sigma \operatorname{wordReadout}(word, b)),\\{}\operatorname{SufficientPhysical}(S) \Rightarrow \operatorname{rank}(\operatorname{S}(Herm0)) \geq \operatorname{dim}(W) - 1,\\{}\exists r, C, O_{i}, \operatorname{SufficientPhysical}(C) \land (\forall i \in \operatorname{Fin}(r), O_{i} \in W) \land (\forall A, \forall i \in \operatorname{Fin}(r), C_{i}(A) = \operatorname{ReTr}(A O_{i})) \land \operatorname{rank}(\operatorname{C}(Herm0)) = r = \operatorname{dim}(W) - 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/ControlledObservableCompletion.controlled_observable_completion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite Hermitian control family and any finite Hermitian readout family on complex matrices of size m, a legal word is a finite list of controls with nonnegative real durations. The empty word is legal. Each segment pulls a readout back by U(t)^* E U(t), where U(t) = exp(-itH). The identity enters as a normalization observable and is not an additional measured readout.

Starting with the real span of the identity and the readouts, adjoining all images under i[H_a,-] reaches an equal consecutive step by m^2 minus the initial real dimension. Every later step is equal. The final Hermitian space is the real span of the identity and all actual legal word readouts, and is the least space containing the initial observables and invariant under every control generator.

Two density matrices have equal terminal expectations for every legal word exactly when their difference annihilates this final space under the trace pairing. A real-linear summary sufficient on physical density states has restriction rank at least dim(W)-1 on trace-zero Hermitian directions. Real trace expectations against a centered orthonormal observable basis attain that rank and are themselves sufficient for every legal prediction. Natural-number subtraction gives zero for m=0, where there are no density states. The rank claim concerns linear expectation summaries.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/ControlledObservableCompletion.controlled_observable_completion`
- Dependency: [D5/S3/Quantum/Dynamics/ConservationAutonomySeparation](ConservationAutonomySeparation.md)
- Dependency: [D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator](HamiltonianEffectCompletionGenerator.md)
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Measurements/VisibleStateSpaceDimension](../Measurements/VisibleStateSpaceDimension.md)
- Dependency: [D5/S3/Quantum/PredictionDepth/FiniteSequentialWordCertificate](../PredictionDepth/FiniteSequentialWordCertificate.md)
