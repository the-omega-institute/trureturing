# Finite Kraus Instrument Born Marginal

## Abstract

Finite normalized Kraus instruments have the expected one-step Born marginal.

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
