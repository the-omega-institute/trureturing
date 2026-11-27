# Actual unordered rooted trees

## Abstract

Actual finite rooted parent trees admit unordered vertex isomorphisms. Their vertex-height and internal-vertex count descend to the finite isomorphism quotient.

**Definition 1.1 (Rooted parent trees).**

$$\operatorname{Tree}\left(V\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Tree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A tree consists of a parent map on its original vertices, a distinguished fixed root, and a proof that every vertex reaches that root after finitely many parent steps. The child relation omits the artificial root loop. No order is imposed on any child fiber.

**Definition 1.2 (Actual vertex isomorphisms).**

$$\operatorname{Iso}\left(T, S\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Iso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An isomorphism is a bijection of the complete original vertex carriers that sends the root to the root and commutes with the parent maps. Thus it preserves and reflects every nonroot child edge.

**Theorem 1.3 (The existing classifier on the whole vertex carrier).**

$$\forall T, S, \operatorname{branchCode}\left(\operatorname{parent}\left(T\right), \operatorname{root}\left(T\right)\right)=\operatorname{branchCode}\left(\operatorname{parent}\left(S\right), \operatorname{root}\left(S\right)\right) \iff \operatorname{Nonempty}\left(\operatorname{Iso}\left(T, S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.code_eq_iff_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertex carriers are arbitrary finite types, independently of one another. A periodic vertex reaching a fixed root must be that root. Consequently transient-child edges are exactly the nonroot parent edges and every original vertex belongs to the root descendant carrier. The existing actual-vertex branch-code classifier therefore applies to the complete vertex sets. Converting its descendant equivalence to a vertex equivalence gives the forward direction; restricting a parent-map isomorphism gives the reverse direction.

**Theorem 1.4 (The depth iterate reaches the root).**

$$\operatorname{iterate}\left(\operatorname{parent}\left(T\right), \operatorname{depth}\left(T, v\right), v\right)=\operatorname{root}\left(T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.reaches_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rooted parent tree and original vertex v, the parent iterate at depth(v) is the root. This is the defining least hitting-time property.

**Theorem 1.5 (Minimality of the depth).**

$$\operatorname{iterate}\left(\operatorname{parent}\left(T\right), k, v\right)=\operatorname{root}\left(T\right) \to \operatorname{depth}\left(T, v\right) \le k$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every iterate reaching the root has index at least the depth of its starting vertex.

**Theorem 1.6 (The root has depth zero).**

$$\operatorname{depth}\left(T, \operatorname{root}\left(T\right)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero iterate already reaches the root when it starts at the root.

**Theorem 1.7 (The nonroot depth step).**

$$v\neq\operatorname{root}\left(T\right) \to \operatorname{depth}\left(T, v\right)=\operatorname{depth}\left(T, \operatorname{parent}\left(T, v\right)\right)+1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonroot original vertex is exactly one level deeper than its parent. Minimality of the two hitting times gives both inequalities.

**Definition 1.8 (Vertex-height).**

$$\operatorname{height}\left(T\right)=1+\operatorname{max}\left(\operatorname{depth}\left(T\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.height` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Depth is the least number of parent steps reaching the root. Vertex-height is one plus its maximum over all original vertices. A nonroot vertex has depth exactly one greater than its parent. Commutation with parent iteration proves depth invariance, and the vertex bijection transports the maximum.

**Definition 1.9 (Internal-vertex count).**

$$\operatorname{internalCount}\left(T\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.internalCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An internal vertex has a nonroot child. The count is the cardinality of this subtype of original vertices. Every actual vertex isomorphism induces a bijection of internal vertices.

**Definition 1.10 (The actual finite quotient).**

$$\operatorname{TreeClass}\left(n\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.treeSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n vertices, take all rooted parent data on Fin n and identify two such data precisely when their branch codes agree. The preceding theorem identifies this equivalence relation with actual unordered rooted vertex isomorphism. The carrier is finite: a datum is determined by its finite parent map and root. Vertex-height and internal-vertex count lift to this quotient by their isomorphism invariance.

**Definition 1.11 (The counting sequence).**

$$\operatorname{a}\left(n\right)=\operatorname{card}\left(\{T: \operatorname{TreeClass}\left(n\right) \mid \operatorname{classHeight}\left(T\right)=\operatorname{classInternalCount}\left(T\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence counts the actual size-n unordered rooted-tree classes whose vertex-height equals their internal-vertex count. Its definition uses this finite isomorphism quotient, without a prescribed recurrence or a restricted family of skeletons.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Iso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Tree`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.a`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.code_eq_iff_iso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_le`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_parent`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_root`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.height`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.internalCount`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.reaches_depth`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.treeSetoid`
- Dependency: [D5/S1/FixedPoints/TransientTrees/RootedVertexClassification](../../../S1/FixedPoints/TransientTrees/RootedVertexClassification.md)
