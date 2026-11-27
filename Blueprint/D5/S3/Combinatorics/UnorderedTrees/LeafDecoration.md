# Reconstructing a rooted tree from its leaf fibres

## Abstract

Internal subtrees with matching original leaf fibres determine an actual rooted isomorphism.

**Definition 1.1 (The internal vertex carrier).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\operatorname{Core}\left(T\right) = \{p: V \mid \operatorname{Internal}\left(T, p\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.Core` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The core is the subtype of the original vertex carrier selected by the internal predicate.

**Definition 1.2 (The original leaf fibre).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(p: \operatorname{Core}\left(T\right)\right) , \left(\operatorname{LeafFibre}\left(T, p\right) = \{x: V \mid \left(\neg \operatorname{Internal}\left(T, x\right)\right) \land \operatorname{Child}\left(T, x, p.val\right)\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.LeafFibre` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fibre consists of the original leaf children of the internal vertex p.

**Definition 1.3 (A finite leaf fibre).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(T: \operatorname{Tree}\left(V\right)\right) \left(p: \operatorname{Core}\left(T\right)\right) , \left(\operatorname{instFintypeLeafFibre}\left(T, p\right): \operatorname{Fintype}\left(\operatorname{LeafFibre}\left(T, p\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.instFintypeLeafFibre` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a finite original vertex type, restricting to the leaf-child predicate supplies the Fintype instance.

**Theorem 1.4 (Extension of the specified core isomorphism).**

$$\forall \left(V: Type\right) \left(W: Type\right) [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(W\right)] \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) , \left(\forall hr: \operatorname{Internal}\left(T, \operatorname{root}\left(T\right)\right), \forall hs: \operatorname{Internal}\left(S, \operatorname{root}\left(S\right)\right), \left(\forall e: \operatorname{Iso}\left(\operatorname{prune}\left(T, hr\right), \operatorname{prune}\left(S, hs\right)\right), \left(\forall p \in \operatorname{Core}\left(T\right),\; \operatorname{card}\left(\operatorname{LeafFibre}\left(T, p\right)\right) = \operatorname{card}\left(\operatorname{LeafFibre}\left(S, e.equiv\left(p\right)\right)\right)\right) \Rightarrow \exists f: \operatorname{Iso}\left(T, S\right), \forall p \in \operatorname{Core}\left(T\right),\; f.equiv\left(p.val\right) = e.equiv\left(p\right).val\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.extendIso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Combine the given isomorphism on the cores with chosen bijections on the corresponding leaf fibres. The resulting isomorphism sends each original internal vertex where the specified core map sends it.

**Theorem 1.5 (Restriction and extension of rooted isomorphisms).**

$$\forall \left(V: Type\right) \left(W: Type\right) [\operatorname{Fintype}\left(V\right)] [\operatorname{Fintype}\left(W\right)] \left(T: \operatorname{Tree}\left(V\right)\right) \left(S: \operatorname{Tree}\left(W\right)\right) , \left(\forall hr: \operatorname{Internal}\left(T, \operatorname{root}\left(T\right)\right), \forall hs: \operatorname{Internal}\left(S, \operatorname{root}\left(S\right)\right), \left(\operatorname{Nonempty}\left(\operatorname{Iso}\left(T, S\right)\right) \Leftrightarrow \left(\exists e: \operatorname{Iso}\left(\operatorname{prune}\left(T, hr\right), \operatorname{prune}\left(S, hs\right)\right), \forall p \in \operatorname{Core}\left(T\right),\; \operatorname{card}\left(\operatorname{LeafFibre}\left(T, p\right)\right) = \operatorname{card}\left(\operatorname{LeafFibre}\left(S, e.equiv\left(p\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.iso_iff_fibres` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An actual isomorphism restricts to the pruned cores and original leaf fibres. Conversely, every original vertex belongs to the core or is a leaf over its unique internal parent. The specified core map and fibre bijections preserve every parent edge and the root.

**Definition 1.6 (The inflated vertex carrier).**

$$\forall \left(V: Type\right) \left(k: V \to \mathbb{N}\right) , \left(\operatorname{Inflated}\left(k\right) = \operatorname{Sum}\left(V, \Sigma p: V, \operatorname{Fin}\left(k\left(p\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.Inflated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier consists of the old vertices and a fresh copy of Fin(k(p)) at each old vertex p.

**Definition 1.7 (Attaching fresh leaves).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(k: V \to \mathbb{N}\right) , \left(\begin{aligned}&\operatorname{inflate}\left(T, k\right): \operatorname{Tree}\left(\operatorname{Inflated}\left(k\right)\right)\\&\operatorname{root}\left(\operatorname{inflate}\left(T, k\right)\right) = \operatorname{inl}\left(\operatorname{root}\left(T\right)\right)\\&\operatorname{parent}\left(\operatorname{inflate}\left(T, k\right), \operatorname{inl}\left(p\right)\right) = \operatorname{inl}\left(\operatorname{parent}\left(T, p\right)\right)\\&\operatorname{parent}\left(\operatorname{inflate}\left(T, k\right), \operatorname{inr}\left(\langle p, i\rangle\right)\right) = \operatorname{inl}\left(p\right)\end{aligned}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.inflate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Old vertices retain their old parent edges. Each fresh leaf points to its fibre index, and the root is the image of the old root.

**Theorem 1.8 (The old vertices become internal).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(k: V \to \mathbb{N}\right) , \left(\forall hk: \left(\forall p \in V,\; \left(\neg \operatorname{Internal}\left(T, p\right)\right) \Rightarrow 0 < k\left(p\right)\right), \forall p \in V,\; \operatorname{Internal}\left(\operatorname{inflate}\left(T, k\right), \operatorname{inl}\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.internal_inflate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An old internal vertex keeps its old child. At an old terminal, a positive leaf multiplicity supplies a fresh child.

**Definition 1.9 (Pruning recovers the skeleton).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(k: V \to \mathbb{N}\right) , \left(\forall hk: \left(\forall p \in V,\; \left(\neg \operatorname{Internal}\left(T, p\right)\right) \Rightarrow 0 < k\left(p\right)\right), \forall hr: \operatorname{Internal}\left(\operatorname{inflate}\left(T, k\right), \operatorname{root}\left(\operatorname{inflate}\left(T, k\right)\right)\right), \operatorname{pruneInflateIso}\left(T, k, hk\right): \operatorname{Iso}\left(T, \operatorname{prune}\left(\operatorname{inflate}\left(T, k\right), hr\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.pruneInflateIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The isomorphism uses the left injection. The proof supplied to prune is internal_inflate at the original root, and the pruned carrier excludes every fresh leaf.

**Definition 1.10 (The prescribed multiplicity of each fibre).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(k: V \to \mathbb{N}\right) , \left(\forall hk: \left(\forall p \in V,\; \left(\neg \operatorname{Internal}\left(T, p\right)\right) \Rightarrow 0 < k\left(p\right)\right), \forall p \in V,\; \operatorname{Fin}\left(k\left(p\right)\right) \equiv \operatorname{LeafFibre}\left(\operatorname{inflate}\left(T, k\right), \operatorname{pruneInflateIso}\left(T, k, hk\right).equiv\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.inflateLeafIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The equivalence sends an index i to the fresh leaf tagged by (p,i) and extracts that index from the corresponding leaf fibre.

**Theorem 1.11 (Size of the inflated carrier).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(k: V \to \mathbb{N}\right) , \left(\operatorname{card}\left(\operatorname{Inflated}\left(k\right)\right) = \operatorname{card}\left(V\right) + \sum_{p \in V} k\left(p\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.card_inflate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum carrier adds one fresh finite leaf fibre per old vertex.

**Theorem 1.12 (An original leaf over a pruned terminal).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\forall hr: \operatorname{Internal}\left(T, \operatorname{root}\left(T\right)\right), \forall p \in \operatorname{Core}\left(T\right),\; \left(\neg \operatorname{Internal}\left(\operatorname{prune}\left(T, hr\right), p\right)\right) \Rightarrow 0 < \operatorname{card}\left(\operatorname{LeafFibre}\left(T, p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.leaf_pos_of_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A child exists in the original tree because p is internal there. If that child were itself internal, it would survive pruning and contradict terminality.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.Core`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.Inflated`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.LeafFibre`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.card_inflate`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.extendIso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.inflate`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.inflateLeafIso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.instFintypeLeafFibre`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.internal_inflate`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.iso_iff_fibres`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.leaf_pos_of_terminal`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/LeafDecoration.pruneInflateIso`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/OneFork](OneFork.md)
