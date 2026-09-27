# Compatible response chain bound

## Abstract

Lagged response quotients assemble a bounded exchange chain.

**Theorem 1.1 (Compatible certificates give a bounded exchange chain).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right), c \in \operatorname{CompatibleCertificate}\left(A, B, R, S, m\right),\; \operatorname{Nonempty}\left(\operatorname{ExchangeChain}\left(\mathit{Nat}, A, B, 2 \cdot m - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgettingBound.compatible_exchange_chain_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive-lag compatible certificate on essential finite count matrices A and B gives a strong-shift-equivalence chain with 2m-1 steps. Thus the shortest chain has length at most 2m-1; no optimality claim is made. The first response matrices meet in a one-step diamond, and the remaining quotient exchanges reach A and B at the lag. At lag one the diamond gives the single exchange.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgettingBound.compatible_exchange_chain_bound`
- Dependency: [D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting](CompatibleResponseForgetting.md)
