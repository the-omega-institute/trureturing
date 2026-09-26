# Equivariant overlap recoding

## Abstract

The boundary transfer supplies an equivariant conjugacy of the two skew-product dynamics.

**Definition 1.1 (Construct the skew-product homeomorphism).**

$$\forall U \in Type, V \in Type, I \in Type, J \in Type, H \in Type, group \in \operatorname{Group}\left(H\right), d \in \operatorname{Boundary}\left(U, V, I, J\right), alpha \in U \to H, topologyU \in \operatorname{TopologicalSpace}\left(U\right), topologyV \in \operatorname{TopologicalSpace}\left(V\right), topologyH \in \operatorname{TopologicalSpace}\left(H\right), continuousGroup \in \operatorname{IsTopologicalGroup}\left(H\right), alphaContinuous \in \operatorname{Continuous}\left(alpha\right),\; \operatorname{Homeomorph}\left(\operatorname{Prod}\left(\operatorname{LeftPath}\left(d\right), H\right), \operatorname{Prod}\left(\operatorname{RightPath}\left(d\right), H\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding.skewHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The path overlap code and the right group-coordinate transfer are constructed together. The inverse reads the preceding half-edge, and both directions are continuous.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/EquivariantOverlapRecoding.skewHomeomorph`
- Dependency: [D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy](BipartiteOverlapConjugacy.md)
