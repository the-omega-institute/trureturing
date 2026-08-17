# Finite Runtime State Cardinality

## Abstract

Finite runtime state components have multiplicative joint cardinality.

**Theorem 1.1 (Finite runtime components have multiplicative cardinality).**

$$\forall C, K, R, M, S,\ [\operatorname{Fintype} C] [\operatorname{Fintype} K] [\operatorname{Fintype} R] [\operatorname{Fintype} M] [\operatorname{Fintype} S],\ \operatorname{card}(C \times K \times R \times M \times S) = \operatorname{card}(C) \times \operatorname{card}(K) \times \operatorname{card}(R) \times \operatorname{card}(M) \times \operatorname{card}(S).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Runtime/FiniteRuntimeStateCardinality.finite_runtime_state_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let C, K, R, M, and S be finite component state types. Their joint runtime state is the product type C times K times R times M times S, and its number of states is the product of the five component cardinalities.

Pinned Mathlib and Loogle returned the exact binary theorem Fintype.card_prod. The Lean proof applies it repeatedly and uses natural-number multiplication associativity only to normalize the result. Repository search found uses of the binary theorem but no equivalent five-component statement. LeanSearch returned HTTP 404 and supplied no search conclusion.

This closes only the finite-state cardinality clause of qdo-v1 theorem/21.1. It does not formalize the source's separate runtime modeling assumptions or its parameter-space bound.

## References

- Truth anchor: `D5/S3/ObserverMemory/Runtime/FiniteRuntimeStateCardinality.finite_runtime_state_cardinality`
