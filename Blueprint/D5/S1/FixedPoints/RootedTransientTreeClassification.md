# Rooted Transient-Tree Classification

## Abstract

Recursive unordered branch codes classify finite transient rooted in-trees.

**Theorem 1.1 (Equal branch codes characterize rooted-tree isomorphism).**

$$\forall Y, Z: \operatorname{Type},\\{}[\operatorname{Fintype}\left(Y\right)], [\operatorname{Fintype}\left(Z\right)],\\{}updateY: Y \to Y, updateZ: Z \to Z,\\{}y: Y, z: Z,\\{}\operatorname{RootedTransientTreeIsomorphic}\left(updateY, updateZ, y, z\right) \iff \operatorname{branchCode}\left(updateY, y\right) = \operatorname{branchCode}\left(updateZ, z\right).$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/RootedTransientTreeClassification.rooted_transient_tree_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let updateY and updateZ be self-maps of finite carriers. A child of a state is constructed as an actual predecessor under its update, with periodic predecessors excluded.

A cycle in the resulting child relation would make its first state periodic. Finiteness therefore makes this relation well-founded, which supports recursion from leaves toward each chosen root.

The branch code recursively forms the unordered multiset of all child codes and applies Mathlib's injective multiset encoding. Rooted isomorphism is defined independently by a one-to-one multiset matching whose paired children are recursively isomorphic.

The forward direction maps every recursive child matching to equal child codes. Conversely, equality of the encoded multisets gives a one-to-one matching of equal child codes, and well-founded induction turns every matched pair into a subtree isomorphism.

Repository and pinned-library searches found no existing unordered finite-tree classifier. The proof directly reuses periodic points, finite acyclic well-foundedness, multiset relational matching, and the injectivity of the pinned multiset encoding.

## References

- Truth anchor: `D5/S1/FixedPoints/RootedTransientTreeClassification.rooted_transient_tree_classification`
