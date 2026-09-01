# Source Contribution Decomposition

## Abstract

Source contributions have unique ordered decompositions exactly when disjoint.

**Theorem 1.1 (Unique source decomposition is equivalent to disjointness).**

$$\begin{aligned}\forall R, Y: \operatorname{Type},\\{}[\operatorname{Ring}(R)], [\operatorname{AddCommGroup}(Y)], [\operatorname{Module}(R, Y)],\\\forall S_{O}, S_{E}: \operatorname{Submodule}(R, Y),\\(\forall y: Y, y \in \operatorname{sup}(S_{O}, S_{E}) \Rightarrow \exists! d: S_{O} \times S_{E}, d_{1} + d_{2} = y) \iff \operatorname{Disjoint}(S_{O}, S_{E}).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Linear/SourceContributionDecomposition.source_contribution_unique_decomposition_iff_disjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the observer and external sources be submodules of the same module. Every element of their sum has an ordered decomposition into one observer contribution and one external contribution.

Such decompositions are unique exactly when the two source submodules are disjoint. Equivalently, the addition map from their product into the ambient module is injective.

## References

- Truth anchor: `D5/S3/Observer/Linear/SourceContributionDecomposition.source_contribution_unique_decomposition_iff_disjoint`
