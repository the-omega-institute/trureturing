# Conservative DAG Embedding

## Abstract

Conservative DAG embeddings compose and preserve dependency reachability.

**Theorem 1.1 (Conservative embeddings preserve reachability).**

$$\forall edgeV: V \to V \to Prop, edgeW: W \to W \to Prop,\\{}embedding: \operatorname{ConservativeEmbedding}\left(edgeV, edgeW\right), first, last: V,\\{}\operatorname{ReflTransGen}\left(edgeV, first, last\right) \Rightarrow\\{}\operatorname{ReflTransGen}\left(edgeW, \operatorname{toFun}\left(embedding, first\right), \operatorname{toFun}\left(embedding, last\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/ConservativeDagEmbedding.map_reachable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let an embedding preserve and reflect direct dependency edges. Every reflexive-transitive path in the source maps to a path between the corresponding embedded endpoints.

The conclusion concerns preservation only. Reflection is carried by the structure binder but is not promoted to a stronger path equivalence in this theorem.

**Theorem 1.2 (Composition maps paths by successive mapping).**

$$\begin{gathered}\forall edgeV: V \to V \to Prop, edgeW: W \to W \to Prop,\\{}edgeZ: Z \to Z \to Prop, \forall firstEmbedding: \operatorname{ConservativeEmbedding}\left(edgeV, edgeW\right),\\{}secondEmbedding: \operatorname{ConservativeEmbedding}\left(edgeW, edgeZ\right), source, target: V,\\{}path: \operatorname{ReflTransGen}\left(edgeV, source, target\right),\\{}(\operatorname{mapReachable}\left(\operatorname{comp}\left(secondEmbedding, firstEmbedding\right), path\right) = \operatorname{mapReachable}\left(secondEmbedding, \operatorname{mapReachable}\left(firstEmbedding, path\right)\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DagSemantics/ConservativeDagEmbedding.map_reachable_comp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quantify two composable conservative embeddings and a source path. Mapping through their composite yields the same proof-irrelevant reachability witness as mapping through them successively.

The equality is between path witnesses for the displayed path; it does not identify the two embedding structures themselves.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/ConservativeDagEmbedding.map_reachable`
- Truth anchor: `D5/S3/ConceptDynamics/DagSemantics/ConservativeDagEmbedding.map_reachable_comp`
