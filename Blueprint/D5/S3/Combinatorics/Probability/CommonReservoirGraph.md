# Graph counts in the common reservoir

## Abstract

Actual rainbow two-edge choices and deterministic predecessor sets are counted on one common reservoir outcome.

**Theorem 1.1 (Rainbow base choices).**

Lean statement: `D5/S3/Combinatorics/Probability/CommonReservoirGraph.graph_base_lower_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/CommonReservoirGraph.graph_base_lower_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a loopless directed graph on a nonempty finite V, with colours in finite C. Require injectivity separately on every outgoing and every incoming star. Let p be in [0,1], nu>0 and n=card(V). For arbitrary u,w, remove the actual exceptional endpoints with more than nu n/16 repeated-colour two-edge choices. Suppose w is outside that set and there are at least nu n/4 actual two-edge middle vertices. If Tb<3p^3 nu n/64, then the probability that fewer than Tb rainbow choices have their middle vertex and both distinct literal colours selected is at most exp(-9p^3 nu n/512).

The deterministic rainbow choice core gives at least 3nu n/16 choices and three classes of disjoint tagged supports. Coincident u=w is included by the same repeated-colour partition count. The triple-selection estimate applies at delta=3/4 with exact mean p^3 times the number of rainbow choices. No assertion that every two-edge choice is rainbow, or that different classes are independent, is used.

**Theorem 1.2 (A fixed predecessor set).**

Lean statement: `D5/S3/Combinatorics/Probability/CommonReservoirGraph.graph_incoming_lower_tail`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Probability/CommonReservoirGraph.graph_incoming_lower_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V,C be finite, p in [0,1], and require proper incoming colours. Fix a deterministic vertex set L and vertex w before sampling. For every delta>=0, the probability that the selected vertex-and-colour incoming count is at most (1-delta)p^2 card(incoming(G,L,w)) is at most exp(-delta^2 p^2 card(incoming(G,L,w))/2). The incoming vertices and colours are distinct, so the actual rows are mutually independent on the common tagged law.

## References

- Truth anchor: `D5/S3/Combinatorics/Probability/CommonReservoirGraph.graph_base_lower_tail`
- Truth anchor: `D5/S3/Combinatorics/Probability/CommonReservoirGraph.graph_incoming_lower_tail`
- Dependency: [D5/S3/Combinatorics/Graph/Rainbow/TwoEdgeChoices](../Graph/Rainbow/TwoEdgeChoices.md)
- Dependency: [D5/S3/Combinatorics/Probability/CommonReservoirRows](CommonReservoirRows.md)
