# Compatible response forgetting

## Abstract

A compatible numbered path certificate constructs an essential finite square graph with both boundaries forgetting after its lag.

**Theorem 1.1 (Incoming lifts respect response depth).**

Lean statement: `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two states with the same numbered path responses at depth d plus one, lifting the same incoming base edge places their predecessor states in one depth-d response class. Appending that edge to each depth-d path identifies the resulting lifted paths with the original depth-(d+1) observations.

Numbered compatible squares give incoming and outgoing lifts on the R-edge states. The two finite sweeps identify their lagged responses with the certificate path bijections; counting their actual edge fibers yields the first row and column response matrices.

**Theorem 1.2 (Compatible certificates give a bounded exchange chain).**

$$\forall n \in \mathit{Nat}, k \in \mathit{Nat}, m \in \mathit{Nat}, A \in \operatorname{CountMat}\left(n, n\right), B \in \operatorname{CountMat}\left(k, k\right), R \in \operatorname{CountMat}\left(n, k\right), S \in \operatorname{CountMat}\left(k, n\right), c \in \operatorname{CompatibleCertificate}\left(A, B, R, S, m\right),\; \operatorname{Nonempty}\left(\operatorname{ExchangeChain}\left(\mathit{Nat}, A, B, 2 \cdot m - 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.compatible_exchange_chain_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive-lag compatible certificate on essential finite count matrices A and B gives a strong-shift-equivalence chain with 2m-1 steps. Thus the shortest chain has length at most 2m-1; no optimality claim is made. Numbered compatible squares determine the two response quotients of the square graph. Their first matrices meet in a one-step diamond, and the remaining quotient exchanges reach A and B at the lag. At lag one the diamond gives the single exchange.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.compatible_exchange_chain_bound`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/CompatibleResponseForgetting.incoming_response_step`
- Dependency: [D5/S3/ConceptDynamics/Coding/FirstResponseDiamond](FirstResponseDiamond.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseQuotientKernel](ResponseQuotientKernel.md)
