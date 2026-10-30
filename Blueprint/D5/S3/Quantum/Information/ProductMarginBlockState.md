# ProductMarginBlockState

## Abstract

Actual subnormalized block-state partial traces

**Theorem 1.1 (Actual subnormalized block-state partial traces).**

$$\forall u:\operatorname{Level}(),\ \forall n:\operatorname{Type}(u),\ {\operatorname{Fintype}(n)\land \operatorname{DecidableEq}(n)}\implies \forall P,Q,K:\operatorname{Matrix}(n, n, \mathbb{C}),\ \operatorname{traceA}(\operatorname{blockMatrix}(P, Q, K))=\frac{(\operatorname{kron}(\operatorname{pointer}(0), P))+(\operatorname{kron}(\operatorname{pointer}(1), Q))}{2}\land \operatorname{traceB}(\operatorname{blockMatrix}(P, Q, K))=\frac{(\operatorname{kron}(\operatorname{pointer}(0), P))+(\operatorname{kron}(\operatorname{pointer}(1), Q))}{2}\land \operatorname{traceAB}(\operatorname{blockMatrix}(P, Q, K))=\frac{(P)+(Q)}{2}\land \operatorname{traceN}(\operatorname{blockMatrix}(P, Q, K))=\operatorname{diagonal}(\operatorname{blockTraces}(P, Q, K))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ProductMarginBlockState.block_partial_traces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Codex CLI (2026). *A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family*. URL: <https://github.com/the-omega-institute/trureturing>.

*Commentary.*

The four blocks are (P-K)/2, K/2, K/2 and (Q-K)/2. The blockState constructor proves positivity and trace one for density states P and Q and an arbitrary complex positive semidefinite common lower matrix K. Tracing out either classical bit gives the same two row sums P/2 and Q/2; tracing out both gives (P+Q)/2. Tracing out the quantum index gives a diagonal AB matrix whose entries are the actual block traces. For unit-trace P and Q, the entries are (1-k)/2, k/2, k/2 and (1-k)/2, with k equal to trace K. Zero blocks remain zero and are never normalized by their own trace. The formula uses traceA, traceB, traceAB and traceN for the indicated index contractions; blockTraces is the function (a,b) to trace(gamma(P,Q,K,a,b)). These partial-trace identities retain every zero block weight.

## References

- Truth anchor: `D5/S3/Quantum/Information/ProductMarginBlockState.block_partial_traces`
- Dependency: [D5/S3/Quantum/Information/QubitNormalFormState](QubitNormalFormState.md)
