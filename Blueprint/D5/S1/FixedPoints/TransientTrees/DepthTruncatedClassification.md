# Depth-Truncated Transient-Tree Classification

## Abstract

Finite-depth branch codes classify truncated transient trees and truncate naturally.

**Theorem 1.1 (Depth codes classify and form a compatible inverse system).**

$$\begin{gathered}\forall Y, Z: \operatorname{Type},\\{}[\operatorname{Fintype}(Y)], [\operatorname{Fintype}(Z)],\\{}\tau: Y \to Y, \sigma: Z \to Z,\\{}h\in \mathbb{N},\\{}(\forall y: Y, z: Z, \operatorname{TruncatedRootedTreeIsomorphic}\left(\tau, \sigma, h, y, z\right) \iff \operatorname{depthBranchCode}\left(\tau, h, y\right) = \operatorname{depthBranchCode}\left(\sigma, h, z\right))\\{}\land\\{}(\forall y: Y, \operatorname{truncateBranchCode}\left(h, \operatorname{depthBranchCode}\left(\tau, h+1, y\right)\right) = \operatorname{depthBranchCode}\left(\tau, h, y\right))\\{}\land\\{}\operatorname{truncateDepthInvariant}\left(h, \operatorname{depthInvariant}\left(h+1, \tau\right)\right) = \operatorname{depthInvariant}\left(h, \tau\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/TransientTrees/DepthTruncatedClassification.depth_truncated_tree_classification_and_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let tau and sigma be self-maps of finite carriers. At depth zero the branch code retains only the root. Each successor depth is the unordered multiset of the preceding-depth codes of every actual nonperiodic predecessor.

The truncated rooted-tree relation is defined independently by a one-to-one recursive matching of those predecessor multisets. Induction on depth identifies that relation exactly with equality of the corresponding branch codes.

Periodic roots are grouped by Mathlib's cyclic periodic orbit. Each component cycle is decorated by its rooted depth codes, and the multiset retains repeated equal necklaces coming from distinct components.

The named truncation maps every child code recursively, every necklace site through the cycle map, and every component through the multiset map. It therefore sends both each depth-successor root code and the full decorated invariant to the preceding depth.

## References

- Truth anchor: `D5/S1/FixedPoints/TransientTrees/DepthTruncatedClassification.depth_truncated_tree_classification_and_naturality`
- Dependency: [D5/S1/FixedPoints/RootedTransientTreeClassification](../RootedTransientTreeClassification.md)
