# Word-Probability Trace Representation

## Abstract

A finite instrument word has matching operational, Schrödinger-trace, and Heisenberg-effect probabilities.

**Theorem 1.1 (Word probability has Schrödinger and Heisenberg trace forms).**

$$\forall d \in Nat, A \in \operatorname{Type}\left(\right), I \in A \to \operatorname{CompletelyPositiveMap}\left(\operatorname{MatrixAlgebra}\left(\operatorname{Fin}\left(d\right)\right), \operatorname{MatrixAlgebra}\left(\operatorname{Fin}\left(d\right)\right)\right), J \in A \to \operatorname{CompletelyPositiveMap}\left(\operatorname{MatrixAlgebra}\left(\operatorname{Fin}\left(d\right)\right), \operatorname{MatrixAlgebra}\left(\operatorname{Fin}\left(d\right)\right)\right), rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), w \in \operatorname{List}\left(A\right),\; \left(\forall g \in A, X \in \operatorname{MatrixAlgebra}\left(\operatorname{Fin}\left(d\right)\right), E \in \operatorname{MatrixAlgebra}\left(\operatorname{Fin}\left(d\right)\right),\; \operatorname{Tr}\left(I\left(g\right)\left(X\right) \cdot E\right) = \operatorname{Tr}\left(X \cdot J\left(g\right)\left(E\right)\right)\right) \Rightarrow \left(\operatorname{operationalWordProbability}\left(I, \operatorname{val}\left(\rho\right), w\right) = \operatorname{Tr}\left(\operatorname{instrumentWordFold}\left(I, \operatorname{val}\left(\rho\right), w\right)\right) \land \operatorname{Tr}\left(\operatorname{instrumentWordFold}\left(I, \operatorname{val}\left(\rho\right), w\right)\right) = \operatorname{Tr}\left(\operatorname{val}\left(\rho\right) \cdot \operatorname{ofMatrix}\left(\operatorname{val}\left(\operatorname{sequentialWordEffect}\left(\operatorname{heisenbergOnHermitianFamily}\left(J\right), w\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/WordProbabilityTraceRepresentation.word_probability_trace_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite word of completely positive instrument branches, the operational probability is evaluated recursively on the current subnormalized branch state. It equals the trace after the full Schrödinger fold.

A supplied trace-duality law pulls each branch back in reverse order. The resulting effect is the imported canonical sequential word effect, obtained by applying the Heisenberg branches to the identity effect.

The formula displays the canonical conversion from the raw Hermitian word effect to the C-star matrix carrier used by the branch maps. This is a data-preserving matrix equivalence, not an implicit change of carrier.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/WordProbabilityTraceRepresentation.word_probability_trace_representation`
- Dependency: [D5/S3/Quantum/Completion/SequentialWordObservationResidual](../Completion/SequentialWordObservationResidual.md)
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/Fibers/OperatorSystemTowerStability](../Fibers/OperatorSystemTowerStability.md)
