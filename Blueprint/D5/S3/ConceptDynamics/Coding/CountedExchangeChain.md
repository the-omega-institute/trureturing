# Counted matrix chains and bounded-window codes

## Abstract

A finite sequence of rectangular exchanges determines an actual conjugacy whose forward and inverse observation windows grow additively.

**Theorem 1.1 (Construct the whole code).**

$$\forall n \in Nat, m \in Nat, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(m, m\right), L \in Nat, c \in \operatorname{ExchangeChain}\left(Nat, A, B, L\right),\; \operatorname{Nonempty}\left(\operatorname{WindowConjugacy}\left(A, B, L\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CountedExchangeChain.chain_has_window_conjugacy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty chain gives the identity. A nonempty chain composes the first counted-edge overlap homeomorphism with the recursively constructed tail. Every intermediate matrix size is retained.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CountedExchangeChain.chain_has_window_conjugacy`
- Dependency: [D5/S3/ConceptDynamics/Coding/CountedMatrixOverlap](CountedMatrixOverlap.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/RectangularNilpotenceBarrier](RectangularNilpotenceBarrier.md)
