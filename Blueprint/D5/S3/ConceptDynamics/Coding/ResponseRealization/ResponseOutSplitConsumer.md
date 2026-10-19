# Consume the response output in the first strict split

## Abstract

The actual numbered response output admits its first strict outgoing split and a shortened total inverse table.

G has finite vertex and edge types, decidable equality on both, and a discrete edge topology. pair has arbitrary natural radii a,b,c,d. The numberedEdgeFintype instance transports finiteness through the existing edgeEquiv, retaining every response edge and all existing parallel numbers. responseCode requires the actual forward seam; its vertex map decodes vertexNumber and its edge map is edgeOutput after existing counted-edge decoding. Endpoint equations are derived from that same numbering.

With hG:Essential G and S:SameTableConjugacy pair, local_of_conjugacy supplies both seams. numberedOutput is genuinely one-block on every counted history. The private inverse-table equation rewrites the existing recovery law using the inverse homeomorphism, so it holds on every target history, rather than only a supplied image.

splitOutput is OutSplitConjugacyDecrease.changed for that exact code and numberedOutput. Its source is the outgoing split of countedGraph along the response edge-output map; its target is the full id outgoing split of G. splitRecover is a total legal-word table with new inverse radii (a+c,b+d), shortened from (a+c,b+d+1). Its construction uses the target essentiality and the complete old recovery, including the final carried edge.

response_recovery supplies the all-history inverse equation used by ResponseTwoSidedConsumer.terminal and ConstructedTowerProfiles.response_profile. The terminal construction obtains its first-stage square directly from OutSplitConjugacyDecrease.square and the actual numbered output. Combining that square with the numbered response equation gives the original-S.forward diagram on each original history.

**Remark 1.1 (numberedEdgeFintype).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.numberedEdgeFintype`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.numberedEdgeFintype` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Transport the finite edge type through the existing edge equivalence. This supplies the actual numbered response presentation and its outgoing constructions.

**Remark 1.2 (responseCode).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.responseCode`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.responseCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructs the actual endpoint-preserving output Code with its finite vertex decoding and unchanged response-edge output. The endpoint proofs use the existing fibre numbering and the supplied seam. splitOutput, splitRecover and the concrete terminal consume it.

**Remark 1.3 (splitOutput).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.splitOutput`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.splitOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Binds the imported changed construction to the actual responseCode and numberedOutput, with the concrete source and target split graphs. The terminal and its profile proof use this homeomorphism.

**Remark 1.4 (splitRecover).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.splitRecover`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.splitRecover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Binds the total outgoing recovery construction to the real code, its one-block equation, target essentiality and old inverse table. ResponseTwoSidedConsumer.terminal and the profile proof use it as Q prime.

**Theorem 1.5 (response_recovery).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.response_recovery`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.response_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the exact recover_window specialization on all split target histories with radii (a+c,b+d). terminal and response_profile pass it as hq prime to their actual reduce tail.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.numberedEdgeFintype`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.responseCode`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.response_recovery`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.splitOutput`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponseOutSplitConsumer.splitRecover`
- Dependency: [D5/S3/ConceptDynamics/Coding/PositiveRecoding/OutSplitNumberedRecoding](../PositiveRecoding/OutSplitNumberedRecoding.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResponseGraphs/OriginalResponseGraph](../ResponseGraphs/OriginalResponseGraph.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/TwoSidedFiniteInduction](../TwoSidedFiniteInduction.md)
