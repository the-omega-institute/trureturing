# Bipartite overlap conjugacy

## Abstract

Rebracketing a legal alternating path preserves every half-edge and gives an invertible code.

**Definition 1.1 (Construct the overlap homeomorphism).**

$$\forall U \in Type, V \in Type, I \in Type, J \in Type, d \in \operatorname{Boundary}\left(U, V, I, J\right), topologyU \in \operatorname{TopologicalSpace}\left(U\right), topologyV \in \operatorname{TopologicalSpace}\left(V\right),\; \operatorname{Homeomorph}\left(\operatorname{LeftPath}\left(d\right), \operatorname{RightPath}\left(d\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy.pathHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The preceding and current half-edges give an explicit inverse in both directions. Coordinate evaluation proves continuity on the legal-path subspaces.

**Theorem 1.2 (The present edge alone is insufficient).**

$$\neg \left(\exists f \in \operatorname{Prod}\left(Bool, Unit\right) \to \operatorname{Prod}\left(Unit, Bool\right),\; \forall x \in \operatorname{LeftPath}\left(binaryBoundary\right),\; f\left(\operatorname{value}\left(x\right)\left(0\right)\right) = \operatorname{value}\left(\operatorname{forward}\left(binaryBoundary, x\right)\right)\left(0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy.no_present_only_recoder` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the one-vertex example with a binary first half-edge, two histories agree at zero and differ at one. Recoding distinguishes them at zero, so no function of the present input edge alone implements this code.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy.no_present_only_recoder`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy.pathHomeomorph`
