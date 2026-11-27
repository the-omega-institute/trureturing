# Actual unordered rooted trees

## Abstract

Actual finite rooted parent trees admit unordered vertex isomorphisms. Their vertex-height and internal-vertex count descend to the finite isomorphism quotient.

**Definition 1.1 (Rooted parent trees).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\begin{aligned}&T: \operatorname{Tree}\left(V\right)\\&\operatorname{parent}\left(T\right): V \to V\\&\operatorname{root}\left(T\right): V\\&\operatorname{parent}\left(T\right)\left(\operatorname{root}\left(T\right)\right) = \operatorname{root}\left(T\right)\\&\forall v \in V,\; \exists k \in \mathbb{N},\; \operatorname{iterate}\left(\operatorname{parent}\left(T\right), k, v\right) = \operatorname{root}\left(T\right)\end{aligned}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Tree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A tree is a parent map on its original vertices with a distinguished fixed root and a proof that every vertex reaches that root after finitely many parent steps. The child relation omits the artificial root loop, and child fibres are unordered.

**Definition 1.2 (Actual vertex isomorphisms).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) \left(e: \operatorname{Iso}\left(T, S\right)\right) , \left(\begin{aligned}&e: \operatorname{Iso}\left(T, S\right)\\&e.equiv: V \equiv W\\&e.equiv\left(\operatorname{root}\left(T\right)\right) = \operatorname{root}\left(S\right)\\&\forall v \in V,\; e.equiv\left(\operatorname{parent}\left(T\right)\left(v\right)\right) = \operatorname{parent}\left(S\right)\left(e.equiv\left(v\right)\right)\end{aligned}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Iso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An isomorphism is a bijection of the complete original vertex carriers that sends the root to the root and commutes with every parent edge.

**Definition 1.3 (Symmetry of rooted isomorphisms).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) \left(e: \operatorname{Iso}\left(T, S\right)\right) , \left(\operatorname{Iso}.\operatorname{symm}\left(e\right): \operatorname{Iso}\left(S, T\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.symm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse vertex equivalence reverses the root and parent-preservation equations.

**Definition 1.4 (Composition of rooted isomorphisms).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(Z: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) \left(R: \operatorname{Tree}\left(Z\right)\right) \left(e: \operatorname{Iso}\left(T, S\right)\right) \left(f: \operatorname{Iso}\left(S, R\right)\right) , \left(\operatorname{Iso}.\operatorname{trans}\left(e, f\right): \operatorname{Iso}\left(T, R\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.trans` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Composition composes the carrier equivalences and the two root-preserving parent-map equations.

**Definition 1.5 (Relabelling a parent tree).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(e: V \equiv W\right) , \left(\begin{aligned}&\operatorname{root}\left(\operatorname{relabel}\left(T, e\right)\right) = e\left(\operatorname{root}\left(T\right)\right)\\&\forall w \in W,\; \operatorname{parent}\left(\operatorname{relabel}\left(T, e\right)\right)\left(w\right) = e\left(\operatorname{parent}\left(T\right)\left(e.symm\left(w\right)\right)\right)\end{aligned}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.relabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Relabelling transports the parent map and root along an equivalence of vertex labels. Reaching the root is transported by iterate semiconjugacy.

**Definition 1.6 (The canonical relabelling isomorphism).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(e: V \equiv W\right) , \left(\operatorname{relabelIso}\left(T, e\right): \operatorname{Iso}\left(T, \operatorname{relabel}\left(T, e\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.relabelIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The relabelling equivalence is itself a rooted vertex isomorphism.

**Definition 1.7 (The nonroot child relation).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(v: V\right) \left(w: V\right) , \left(\left(\operatorname{Child}\left(T, v, w\right)\right) \Leftrightarrow \left(\left(v \ne \operatorname{root}\left(T\right)\right) \land \left(\operatorname{parent}\left(T, v\right) = w\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Child` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Child excludes the fixed root loop and records exactly one parent edge.

**Definition 1.8 (Internal vertices).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(v: V\right) , \left(\left(\operatorname{Internal}\left(T, v\right)\right) \Leftrightarrow \left(\exists w \in V,\; \operatorname{Child}\left(T, w, v\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Internal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An internal vertex has an actual nonroot child.

**Definition 1.9 (Vertex depth).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(v: V\right) , \left(\operatorname{depth}\left(T, v\right) = \min_{k \mid \operatorname{iterate}\left(\operatorname{parent}\left(T\right), k, v\right) = \operatorname{root}\left(T\right)}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Depth is the least natural iterate index at which the parent map reaches the fixed root.

**Theorem 1.10 (The depth iterate reaches the root).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(v: V\right) , \left(\operatorname{iterate}\left(\operatorname{parent}\left(T\right), \operatorname{depth}\left(T, v\right), v\right) = \operatorname{root}\left(T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.reaches_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parent iterate at depth(v) reaches the root by the defining least-hitting-time witness.

**Theorem 1.11 (Minimality of the depth).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(v: V\right) \left(k: \mathbb{N}\right) , \left(\left(\operatorname{iterate}\left(\operatorname{parent}\left(T\right), k, v\right) = \operatorname{root}\left(T\right)\right) \Rightarrow \left(\operatorname{depth}\left(T, v\right) \le k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every iterate reaching the root has index at least the depth.

**Theorem 1.12 (The root has depth zero).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\operatorname{depth}\left(T, \operatorname{root}\left(T\right)\right) = 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_root` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero iterate already reaches the root when the starting vertex is the root.

**Theorem 1.13 (The nonroot depth step).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(v: V\right) , \left(\left(v \ne \operatorname{root}\left(T\right)\right) \Rightarrow \left(\operatorname{depth}\left(T, v\right) = \operatorname{depth}\left(T, \operatorname{parent}\left(T, v\right)\right) + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_parent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonroot vertex is one level deeper than its parent.

**Theorem 1.14 (Isomorphisms preserve child edges).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) \left(e: \operatorname{Iso}\left(T, S\right)\right) \left(a: V\right) \left(b: V\right) , \left(\left(\operatorname{Child}\left(T, a, b\right)\right) \Leftrightarrow \left(\operatorname{Child}\left(S, e.equiv\left(a\right), e.equiv\left(b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.iso_child` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Root preservation and parent commutation preserve and reflect the actual child relation.

**Theorem 1.15 (The whole-carrier branch-code classifier).**

$$\forall \left(V: Type\right) \left(W: Type\right) [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(W\right)] \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) , \left(\left(\operatorname{branchCode}\left(\operatorname{parent}\left(T\right), \operatorname{root}\left(T\right)\right) = \operatorname{branchCode}\left(\operatorname{parent}\left(S\right), \operatorname{root}\left(S\right)\right)\right) \Leftrightarrow \left(\operatorname{Nonempty}\left(\operatorname{Iso}\left(T, S\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.code_eq_iff_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing transient-tree classifier applies to the complete original carrier after the root descendant bridge. Restricting a parent-map isomorphism gives the reverse direction.

**Theorem 1.16 (Isomorphisms preserve depth).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) \left(e: \operatorname{Iso}\left(T, S\right)\right) \left(v: V\right) , \left(\operatorname{depth}\left(S, e.equiv\left(v\right)\right) = \operatorname{depth}\left(T, v\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.iso_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterate semiconjugacy and root preservation identify the two least hitting times.

**Theorem 1.17 (Isomorphisms preserve internality).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) \left(e: \operatorname{Iso}\left(T, S\right)\right) \left(v: V\right) , \left(\left(\operatorname{Internal}\left(T, v\right)\right) \Leftrightarrow \left(\operatorname{Internal}\left(S, e.equiv\left(v\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.iso_internal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The child-edge equivalence transports the existence of an actual child.

**Definition 1.18 (The internal-vertex equivalence).**

$$\forall \left(V: Type\right) \left(W: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) \left(e: \operatorname{Iso}\left(T, S\right)\right) , \left(\operatorname{internalEquiv}\left(e\right): \{v: V \mid \operatorname{Internal}\left(T, v\right)\} \equiv \{v: W \mid \operatorname{Internal}\left(S, v\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.internalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier equivalence restricts to the subtypes of internal vertices.

**Definition 1.19 (Vertex-height).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\operatorname{height}\left(T\right) = \max_{v \in V} \operatorname{depth}\left(T, v\right)+1\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.height` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertex-height is one plus the maximum depth over the finite original carrier.

**Definition 1.20 (Internal-vertex count).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\operatorname{internalCount}\left(T\right) = \operatorname{card}\left(\{v: V \mid \operatorname{Internal}\left(T, v\right)\}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.internalCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The count is the finite cardinality of the subtype of original internal vertices.

**Theorem 1.21 (Isomorphisms preserve vertex-height).**

$$\forall \left(V: Type\right) \left(W: Type\right) [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(W\right)] \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) \left(e: \operatorname{Iso}\left(T, S\right)\right) , \left(\operatorname{height}\left(T\right) = \operatorname{height}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ParentTree.iso_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The depth equivalence transports the finite maximum across the carrier equivalence.

**Definition 1.22 (The parent-data setoid).**

$$\forall \left(n: \mathbb{N}\right) \left(T: \operatorname{Tree}\left(\operatorname{Fin}\left(n\right)\right)\right) \left(S: \operatorname{Tree}\left(\operatorname{Fin}\left(n\right)\right)\right) , \left(\left(\operatorname{treeSetoid}\left(n\right).r\left(T, S\right)\right) \Leftrightarrow \left(\operatorname{branchCode}\left(\operatorname{parent}\left(T\right), \operatorname{root}\left(T\right)\right) = \operatorname{branchCode}\left(\operatorname{parent}\left(S\right), \operatorname{root}\left(S\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.treeSetoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On parent data over Fin n, the relation is equality of complete branch codes with the chosen root.

**Definition 1.23 (The actual unordered class carrier).**

$$\forall \left(n: \mathbb{N}\right) , \left(\operatorname{TreeClass}\left(n\right) = \operatorname{Quotient}\left(\operatorname{treeSetoid}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.TreeClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TreeClass is the quotient of all rooted parent data on Fin n by the full root- and parent-preserving vertex-isomorphism relation.

**Definition 1.24 (Finiteness of parent data).**

$$\forall \left(n: \mathbb{N}\right) , \left(\operatorname{fintypeTree}\left(n\right): \operatorname{Fintype}\left(\operatorname{Tree}\left(\operatorname{Fin}\left(n\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.fintype_tree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite parent map and root data on Fin n form a finite type.

**Definition 1.25 (Finiteness of unordered classes).**

$$\forall \left(n: \mathbb{N}\right) , \left(\operatorname{fintypeClasses}\left(n\right): \operatorname{Fintype}\left(\operatorname{TreeClass}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.fintype_classes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quotient carrier inherits a finite type from the finite parent-data carrier.

**Definition 1.26 (Class vertex-height).**

$$\forall \left(n: \mathbb{N}\right) \left(T: \operatorname{Tree}\left(\operatorname{Fin}\left(n\right)\right)\right) , \left(\operatorname{classHeight}\left([T]\right) = \operatorname{height}\left(T\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.classHeight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vertex-height descends to the quotient because actual vertex isomorphisms preserve it.

**Definition 1.27 (Class internal-vertex count).**

$$\forall \left(n: \mathbb{N}\right) \left(T: \operatorname{Tree}\left(\operatorname{Fin}\left(n\right)\right)\right) , \left(\operatorname{classInternalCount}\left([T]\right) = \operatorname{internalCount}\left(T\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.classInternalCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Internal-vertex count descends to the quotient through the internal subtype equivalence.

**Definition 1.28 (The counting sequence).**

$$\forall \left(n: \mathbb{N}\right) , \left(\operatorname{a}\left(n\right) = \operatorname{card}\left(\{T: \operatorname{TreeClass}\left(n\right) \mid \operatorname{classHeight}\left(T\right) = \operatorname{classInternalCount}\left(T\right)\}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ParentTree.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sequence counts the actual size-n unordered rooted-tree classes whose vertex-height equals their internal-vertex count. The defining subtype predicate is stated in the source result and preserved by the class observables.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Child`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Internal`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Iso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.Tree`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.TreeClass`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.a`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.classHeight`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.classInternalCount`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.code_eq_iff_iso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_le`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_parent`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.depth_root`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.fintype_classes`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.fintype_tree`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.height`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.internalCount`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.internalEquiv`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.iso_child`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.iso_depth`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.iso_height`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.iso_internal`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.reaches_depth`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.relabel`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.relabelIso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.symm`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.trans`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ParentTree.treeSetoid`
- Dependency: [D5/S1/FixedPoints/TransientTrees/RootedVertexClassification](../../../S1/FixedPoints/TransientTrees/RootedVertexClassification.md)
