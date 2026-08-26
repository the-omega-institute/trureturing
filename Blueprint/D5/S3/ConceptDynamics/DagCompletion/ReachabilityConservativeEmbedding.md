# Reachability-Conservative Embedding

## Abstract

Reachability-conservative embeddings preserve and reflect prerequisite and consequence closures.

**Theorem 1.1 (Prerequisite closure is preserved and reflected on the image).**

$$\begin{gathered}\forall edgeV: V \to V \to Prop, edgeW: W \to W \to Prop,\\{}\forall embedding: \operatorname{ReachabilityEmbedding}\left(edgeV, edgeW\right), targets: \operatorname{Set}\left(V\right), node: V,\\{}\operatorname{toFun}\left(embedding, node\right) \in \operatorname{prerequisiteClosure}\left(edgeW, \operatorname{image}\left(\operatorname{toFun}\left(embedding\right), targets\right)\right) \iff\\{}node \in \operatorname{prerequisiteClosure}\left(edgeV, targets\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/ReachabilityConservativeEmbedding.mem_prerequisiteClosure_image_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quantify a reachability-preserving and reachability-reflecting embedding. An embedded node belongs to the target image's prerequisite closure exactly when the original node belongs to the original closure.

The equivalence is restricted to nodes in the source carrier and target sets transported by the embedding image.

**Theorem 1.2 (Consequence closure is preserved and reflected on the image).**

$$\begin{gathered}\forall edgeV: V \to V \to Prop, edgeW: W \to W \to Prop,\\{}\forall embedding: \operatorname{ReachabilityEmbedding}\left(edgeV, edgeW\right), sources: \operatorname{Set}\left(V\right), node: V,\\{}\operatorname{toFun}\left(embedding, node\right) \in \operatorname{consequenceClosure}\left(edgeW, \operatorname{image}\left(\operatorname{toFun}\left(embedding\right), sources\right)\right) \iff\\{}node \in \operatorname{consequenceClosure}\left(edgeV, sources\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagCompletion/ReachabilityConservativeEmbedding.mem_consequenceClosure_image_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same structure identifies consequence-closure membership after mapping the source set into the target carrier.

No statement is made about target-carrier nodes outside the embedding's image.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/ReachabilityConservativeEmbedding.mem_consequenceClosure_image_iff`
- Truth anchor: `D5/S3/ConceptDynamics/DagCompletion/ReachabilityConservativeEmbedding.mem_prerequisiteClosure_image_iff`
- Dependency: [D5/S3/ConceptDynamics/DagCompletion/ConsequenceClosure](ConsequenceClosure.md)
- Dependency: [D5/S3/ConceptDynamics/DependencyTopology/DependencyReachabilityOrder](../DependencyTopology/DependencyReachabilityOrder.md)
