# Rooted Vertex Reconstruction

## Abstract

Equal branch codes reconstruct actual rooted vertices and internal child edges.

**Definition 1.1 (Original descendant vertices).**

$$\begin{gathered}u \operatorname{universe}, \forall Y: \operatorname{Type}_{u}, f: Y \to Y, r: Y,\\{}\operatorname{Descendant}\left(f, r\right):= \{ x: Y \mid \operatorname{ReflTransGen}\left(\operatorname{TransientChild}\left(f\right), x, r\right) \}\end{gathered}$$

*Formalization.* `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.Descendant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier is a subtype of the original state space. The root is included by the reflexive path. TransientChild is the existing nonperiodic-child relation, directed toward the parent; val denotes subtype projection.

**Definition 1.2 (Root-preserving vertex equivalence).**

$$\begin{gathered}u, v \operatorname{universes},\\{}\forall Y: \operatorname{Type}_{u}, Z: \operatorname{Type}_{v},\\{}\forall f: Y \to Y, g: Z \to Z, r: Y, s: Z,\\{}\operatorname{RootedVertexEquiv}(f, g, r, s) \operatorname{fields}:\\{}\operatorname{equiv}: \operatorname{Equiv}\left(\operatorname{Descendant}\left(f, r\right), \operatorname{Descendant}\left(g, s\right)\right),\\{}\operatorname{rootEq}: \operatorname{equiv}\left(\langle r, \operatorname{refl}\rangle\right)=\langle s, \operatorname{refl}\rangle,\\{}\operatorname{childIff}: \forall a, b: \operatorname{Descendant}\left(f, r\right), \operatorname{TransientChild}\left(f, \operatorname{val}\left(a\right), \operatorname{val}\left(b\right)\right) \iff \operatorname{TransientChild}\left(g, \operatorname{val}\left(\operatorname{equiv}\left(a\right)\right), \operatorname{val}\left(\operatorname{equiv}\left(b\right)\right)\right)\end{gathered}$$

*Formalization.* `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.RootedVertexEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed equiv, rootEq, and childIff denote the Lean fields equiv, root_eq, and child_iff. The equivalence includes both inverse laws. This definition requires no finiteness instances; finiteness is used by the reconstruction theorem.

**Definition 1.3 (Root and disjoint child subtrees).**

$$\begin{gathered}u \operatorname{universe}, \forall Y: \operatorname{Type}_{u}, [\operatorname{Finite}\left(Y\right)],\\{}\forall f: Y \to Y, r: Y,\\{}p:= \operatorname{descendantPartition}\left(f, r\right): \operatorname{Equiv}\left(\operatorname{Option}\left(\operatorname{Sigma}_{c: \{ c: Y \mid \operatorname{TransientChild}\left(f, c, r\right) \}} \operatorname{Descendant}\left(f, \operatorname{val}\left(c\right)\right)\right), \operatorname{Descendant}\left(f, r\right)\right),\\{}\operatorname{p}\left(\operatorname{none}\right)=\langle r, \operatorname{refl}\rangle,\\{}\forall c: \{ c: Y \mid \operatorname{TransientChild}\left(f, c, r\right) \}, x: \operatorname{Descendant}\left(f, \operatorname{val}\left(c\right)\right), \operatorname{val}\left(\operatorname{p}\left(\operatorname{some}\left(\langle c, x\rangle\right)\right)\right)=\operatorname{val}\left(x\right),\\{}\forall a: \operatorname{Option}\left(\operatorname{Sigma}_{c: \{ c: Y \mid \operatorname{TransientChild}\left(f, c, r\right) \}} \operatorname{Descendant}\left(f, \operatorname{val}\left(c\right)\right)\right), \operatorname{inverse}\left(p, \operatorname{p}\left(a\right)\right)=a,\\{}\forall x: \operatorname{Descendant}\left(f, r\right), \operatorname{p}\left(\operatorname{inverse}\left(p, x\right)\right)=x\end{gathered}$$

*Formalization.* `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.descendantPartition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Option value none denotes the root. A some value carries an actual immediate child and an original vertex below that child. Deterministic parents make paths comparable; well-foundedness excludes a return to the root and forces the immediate child to be unique. The resulting bijection supplies the inverse used in reconstruction.

**Theorem 1.4 (Equal branch codes reconstruct rooted vertices).**

$$\begin{gathered}u, v \operatorname{universes},\\{}\forall Y: \operatorname{Type}_{u}, Z: \operatorname{Type}_{v},\\{}[\operatorname{Fintype}\left(Y\right)], [\operatorname{Fintype}\left(Z\right)],\\{}\forall f: Y \to Y, g: Z \to Z, r: Y, s: Z,\\{}\operatorname{branchCode}\left(f, r\right)=\operatorname{branchCode}\left(g, s\right) \implies\\{}\exists e: \operatorname{Equiv}\left(\operatorname{Descendant}\left(f, r\right), \operatorname{Descendant}\left(g, s\right)\right),\\{}\operatorname{e}\left(\langle r, \operatorname{refl}\rangle\right)=\langle s, \operatorname{refl}\rangle \land\\{}(\forall a, b: \operatorname{Descendant}\left(f, r\right), \operatorname{TransientChild}\left(f, \operatorname{val}\left(a\right), \operatorname{val}\left(b\right)\right) \iff \operatorname{TransientChild}\left(g, \operatorname{val}\left(\operatorname{e}\left(a\right)\right), \operatorname{val}\left(\operatorname{e}\left(b\right)\right)\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.rooted_vertex_equiv_of_branch_code_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RootedVertexEquiv stores precisely the displayed equivalence, root equality, and child-relation iff in its equiv, root_eq, and child_iff fields. The theorem asserts that this structure is nonempty. The two universes are independent, and no equality of ambient cardinalities is assumed.

Equality of encoded child multisets matches occurrences with their full multiplicities. Well-founded recursion constructs the child equivalences. The actual partition inverse, the dependent sum of those equivalences, and the target partition form the vertex equivalence. The edge proof includes both internal subtree edges and edges from child roots to the root.

An arbitrary root may be transient, and its outgoing update may leave this carrier. The result asserts only the displayed internal child relation. The converse classification, cycle and component gluing, cardinal-depth saturation, and the compatible-family inverse are separate obligations.

**Theorem 1.5 (Recursive matching reconstructs the same vertices).**

$$\begin{gathered}u, v \operatorname{universes},\\{}\forall Y: \operatorname{Type}_{u}, Z: \operatorname{Type}_{v},\\{}[\operatorname{Fintype}\left(Y\right)], [\operatorname{Fintype}\left(Z\right)],\\{}\forall f: Y \to Y, g: Z \to Z, r: Y, s: Z,\\{}\operatorname{RootedTransientTreeIsomorphic}\left(f, g, r, s\right) \implies\\{}\exists e: \operatorname{Equiv}\left(\operatorname{Descendant}\left(f, r\right), \operatorname{Descendant}\left(g, s\right)\right),\\{}\operatorname{e}\left(\langle r, \operatorname{refl}\rangle\right)=\langle s, \operatorname{refl}\rangle \land\\{}(\forall a, b: \operatorname{Descendant}\left(f, r\right), \operatorname{TransientChild}\left(f, \operatorname{val}\left(a\right), \operatorname{val}\left(b\right)\right) \iff \operatorname{TransientChild}\left(g, \operatorname{val}\left(\operatorname{e}\left(a\right)\right), \operatorname{val}\left(\operatorname{e}\left(b\right)\right)\right))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.rooted_vertex_equiv_of_recursive_isomorphism` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing recursive Multiset.Rel predicate gives equal branch codes by the frozen classifier, so the same reconstruction applies.

## References

- Truth anchor: `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.Descendant`
- Truth anchor: `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.RootedVertexEquiv`
- Truth anchor: `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.descendantPartition`
- Truth anchor: `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.rooted_vertex_equiv_of_branch_code_eq`
- Truth anchor: `D5/S1/FixedPoints/TransientTrees/RootedVertexReconstruction.rooted_vertex_equiv_of_recursive_isomorphism`
- Dependency: [D5/S1/FixedPoints/RootedTransientTreeClassification](../RootedTransientTreeClassification.md)
