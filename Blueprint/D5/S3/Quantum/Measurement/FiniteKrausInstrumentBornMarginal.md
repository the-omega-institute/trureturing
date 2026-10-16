# Finite Kraus Instrument Born Marginal

## Abstract

Finite normalized Kraus instruments have the expected one-step Born marginal.

For a finite adaptive protocol, associate a normalized instrument with each actual outcome prefix. Starting from a density matrix, apply the selected branch map to obtain the next subnormalized state. Each branch remains positive. The trace is its prefix probability, and summing the traces of the immediate children recovers the parent trace. Induction on the finite outcome tree, including leaves that terminate early, gives total leaf probability one.

For a branch of strictly positive trace, division by that real trace gives a positive matrix of trace one. No conditional state is assigned by this formula to a zero-probability branch. For an arbitrary final effect, trace cyclicity replaces each forward Kraus sandwich by the corresponding adjoint sandwich acting on the effect. Reversing the finite branch sequence yields the reference-boundary pullback and preserves its joint probability.

Adaptivity changes the chosen instrument as a function of the actual prefix; it does not change either trace identity. Any environment that can interact again is part of the current quantum interface. A permanently discarded Kraus label is not available for later feedback. The complete-subtree identity in FiniteLocalProtocol permits finite branching and variable stopping depth; WordProbabilityTraceRepresentation supplies the finite Schrödinger and Heisenberg folds.

**Theorem 1.1 (A finite Kraus branch has the Born weight of its effect).**

$$\forall n, X, A, R: \operatorname{Type},\\{}\operatorname{Fintype}(n), \operatorname{Nonempty}(n), \operatorname{DecidableEq}(n),\\{}\operatorname{Fintype}(A), \operatorname{Fintype}(R),\\{}K: \{K: X \to A \to R \to \operatorname{Matrix}(n, n, \mathbb{C}) \mid \forall x \in X,\; \sum_{a \in A} \sum_{r \in R} \operatorname{star}(K(x, a, r)) \cdot K(x, a, r) = \operatorname{identityMatrix}(n)\},\\{}\rho: \operatorname{DensityState}(n),\\{}\forall x: X, a: A,\\{}\operatorname{let} S: \operatorname{Matrix}(n, n, \mathbb{C}) = \operatorname{matrix}(\rho),\\{}B: \operatorname{Matrix}(n, n, \mathbb{C}) = \sum_{r \in R} K(x, a, r) \cdot S \cdot \operatorname{star}(K(x, a, r)),\\{}E: \operatorname{Matrix}(n, n, \mathbb{C}) = \sum_{r \in R} \operatorname{star}(K(x, a, r)) \cdot K(x, a, r);\\{}\operatorname{Tr}(B) = \operatorname{bornProbability}(S, E).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.finite_kraus_instrument_born_marginal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public Kraus family is normalized at every setting, so its outcome branches form a finite-dimensional instrument. The input uses the canonical positive trace-one density-state carrier.

Each branch and effect is constructed by a finite Kraus sum. Trace linearity and cyclicity move the outer Kraus operator across the trace, yielding the canonical Born trace pairing.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/FiniteKrausInstrumentBornMarginal.finite_kraus_instrument_born_marginal`
- Dependency: [D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition](../Divergence/QuantumRelativeEntropyDefectComposition.md)
- Dependency: [D5/S3/Quantum/Measurement/StaticEffectSequentialSeparation](StaticEffectSequentialSeparation.md)
