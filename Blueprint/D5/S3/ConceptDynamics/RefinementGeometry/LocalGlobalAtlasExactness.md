# Local-Global Atlas Exactness

## Abstract

Canonical local-global exactness is separation plus gluing, independently.

**Theorem 1.1 (Atlas exactness splits into independent separation and gluing clauses).**

$$\left(\forall X \in Type, A \in \operatorname{RefinementSystem}\left(X\right),\; \operatorname{Bijective}\left(\operatorname{stateThread}\left(A\right)\right) \Leftrightarrow \left(\operatorname{ker}\left(\operatorname{stateThread}\left(A\right)\right) = \operatorname{diagonal}\left(X\right) \land \operatorname{range}\left(\operatorname{stateThread}\left(A\right)\right) = \operatorname{univ}\left(\operatorname{InverseThread}\left(A\right)\right)\right)\right) \land \left(\left(\exists A \in \operatorname{RefinementSystem}\left(Bool\right),\; \operatorname{ker}\left(\operatorname{stateThread}\left(A\right)\right) = \operatorname{diagonal}\left(Bool\right) \land \operatorname{range}\left(\operatorname{stateThread}\left(A\right)\right) \ne \operatorname{univ}\left(\operatorname{InverseThread}\left(A\right)\right)\right) \land \left(\exists A \in \operatorname{RefinementSystem}\left(Bool\right),\; \operatorname{range}\left(\operatorname{stateThread}\left(A\right)\right) = \operatorname{univ}\left(\operatorname{InverseThread}\left(A\right)\right) \land \operatorname{ker}\left(\operatorname{stateThread}\left(A\right)\right) \ne \operatorname{diagonal}\left(Bool\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementGeometry/LocalGlobalAtlasExactness.local_global_atlas_exactness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every refinement system, stateThread is the canonical map from a global state to its compatible inverse-limit thread. Its kernel being diagonal is the separation clause; its range being all threads is the gluing clause.

Bijectivity is equivalent to the conjunction of those exact kernel and range statements. The theorem exposes the canonical map directly.

Two explicit refinement systems on Bool establish logical independence: one has diagonal kernel but non-full range, and one has full range but non-diagonal kernel.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementGeometry/LocalGlobalAtlasExactness.local_global_atlas_exactness`
- Dependency: [D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion](InverseLimitCompletion.md)
