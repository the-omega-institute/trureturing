# Diagonal Phase Blindness

## Abstract

Diagonal observable families cannot recover relative phase without a non-diagonal interface.

**Theorem 1.1 (Diagonal observables cannot recover relative phase).**

$$\begin{aligned}\forall I: \operatorname{Type},\\(\forall observable: I \to QubitMatrix, (\forall i: I, \operatorname{IsDiag}\left(\operatorname{observable}\left(i\right)\right)) \Rightarrow\\{}equalSuperpositionDensity \ne \operatorname{mul}\left(\operatorname{mul}\left(qubitZ, equalSuperpositionDensity\right), qubitZ\right) \land \operatorname{apply}\left(\operatorname{jointReadout}\left(\operatorname{fun}\left(i, rho, \operatorname{bornProbability}\left(rho, \operatorname{observable}\left(i\right)\right)\right)\right), equalSuperpositionDensity\right) = \operatorname{apply}\left(\operatorname{jointReadout}\left(\operatorname{fun}\left(i, rho, \operatorname{bornProbability}\left(rho, \operatorname{observable}\left(i\right)\right)\right)\right), \operatorname{mul}\left(\operatorname{mul}\left(qubitZ, equalSuperpositionDensity\right), qubitZ\right)\right))\\\land (\forall A: QubitMatrix, \operatorname{bornProbability}\left(equalSuperpositionDensity, A\right) \ne \operatorname{bornProbability}\left(\operatorname{mul}\left(\operatorname{mul}\left(qubitZ, equalSuperpositionDensity\right), qubitZ\right), A\right) \Rightarrow \neg \operatorname{IsDiag}\left(A\right))\\\land (\neg \operatorname{IsDiag}\left(qubitX\right) \land \operatorname{bornProbability}\left(equalSuperpositionDensity, qubitX\right) \ne \operatorname{bornProbability}\left(\operatorname{mul}\left(\operatorname{mul}\left(qubitZ, equalSuperpositionDensity\right), qubitZ\right), qubitX\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/DiagonalPhaseBlindness.diagonal_prime_observables_cannot_recover_relative_phase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equal superposition density and its conjugate by the canonical phase flip are distinct. Every indexed family of diagonal matrices gives the same joint trace-expectation readout on this pair, regardless of the size of the index type.

The second public clause uses the same pair: any matrix whose expectation separates the two states cannot be diagonal. The canonical Pauli X matrix supplies such a non-diagonal interface explicitly.

The family readout, trace expectation, diagonal predicate, states, and interface are existing repository or pinned-library primitives; no parallel observation carrier is introduced.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/DiagonalPhaseBlindness.diagonal_prime_observables_cannot_recover_relative_phase`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../../ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion.md)
- Dependency: [D5/S3/Quantum/QubitWitnesses](../QubitWitnesses.md)
