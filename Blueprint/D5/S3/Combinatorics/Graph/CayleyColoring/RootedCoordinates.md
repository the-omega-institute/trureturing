# Rooted tree color coordinates

## Abstract

A zero color-difference mark identifies a conflict at the edge to the parent.

**Theorem 1.1 (Zero marks and equal colors).**

$$\forall (V: Type), \forall (A: Type), [\operatorname{AddGroup}\left(A\right)] \forall (T: \operatorname{Tree}\left(V\right)), \forall (r: V), \forall (c: V \to A), \forall (x: \operatorname{Away}\left(V, r\right)), \operatorname{snd}\left(\operatorname{edgeColorEquiv}\left(T, r\right)\left(c\right)\right)\left(\operatorname{edgeEquiv}\left(T, r, x\right)\right) = 0 \iff c\left(\operatorname{val}\left(x\right)\right) = c\left(\operatorname{parent}\left(T, r, x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.zero_pattern_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

Each non-root vertex indexes its edge to its parent. The color equivalence stores the root color and the differences on these edges. Evaluation at the indexed edge gives zero exactly when the endpoints started with the same color. This is the edge-coordinate version of the independent conflicts used in Theorem 10.

**Definition 1.2 (Away).**

$$\forall (V: \mathit{Type}), \forall (r: V), (\mathit{Away} V r : \mathit{Type} (\mathit{max} 0 u)) = \{ v : V  |  v \neq r \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.Away` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.3 (Edge Color Equiv).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{AddGroup} A] \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), (\mathit{edgeColorEquiv} V A T r : (V \to A) \equiv A \times (\mathit{val} (\mathit{val} T).\mathit{edgeSet} \to A)) = (\mathit{colorEquiv} T r).\mathit{trans} ((\mathit{Equiv}.\mathit{refl} A).\mathit{prodCongr} ((\mathit{edgeEquiv} T r).\mathit{arrowCongr} (\mathit{Equiv}.\mathit{refl} A)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edgeColorEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.4 (Edge Equiv).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), (\mathit{edgeEquiv} V T r : \mathit{CayleyColors}.\mathit{Away} r \equiv \mathit{val} (\mathit{val} T).\mathit{edgeSet}) = \mathit{Equiv}.\mathit{ofBijective} (\mathit{fun} (v : \mathit{Away} r) => \mathit{edgeFromPair} T v.\mathit{val} (\mathit{parent} T r v))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.5 (Edge orientation).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (v: V), \forall (w: V), \forall (h: (\mathit{val} T).\mathit{Adj} v w), (\exists (\mathit{hv} : v \neq r), \mathit{parent} T r \langle v, \mathit{hv}\rangle = w) \lor \exists (\mathit{hw} : w \neq r), \mathit{parent} T r \langle w, \mathit{hw}\rangle = v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edge_orientation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.6 (Parent).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (v: \mathit{CayleyColors}.\mathit{Away} r), (\mathit{parent} V T r v : V) = \mathit{choose} (\mathit{fun} (x : V) => T.\mathit{val}.\mathit{Adj} v.\mathit{val} x \land T.\mathit{val}.\mathit{dist} r x < T.\mathit{val}.\mathit{dist} r v.\mathit{val})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The parent is the unique adjacent vertex at smaller distance from the root.

**Theorem 1.7 (Parent spec).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (v: \mathit{CayleyColors}.\mathit{Away} r), (\mathit{val} T).\mathit{Adj} (\mathit{val} v) (\mathit{parent} T r v) \land (\mathit{val} T).\mathit{dist} r (\mathit{parent} T r v) < (\mathit{val} T).\mathit{dist} r \mathit{val} v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.8 (Parent unique).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (v: \mathit{CayleyColors}.\mathit{Away} r), \forall (w: V), \forall (\mathit{hadj}: (\mathit{val} T).\mathit{Adj} (\mathit{val} v) w), \forall (\mathit{hlt}: (\mathit{val} T).\mathit{dist} r w < (\mathit{val} T).\mathit{dist} r \mathit{val} v), w = \mathit{parent} T r v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.9 (Reconstruct).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{AddGroup} A] \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (\mathit{base}: A), \forall (\mathit{diff}: \mathit{CayleyColors}.\mathit{Away} r \to A), \forall (v: V), (\mathit{reconstruct} V A T r \mathit{base} \mathit{diff} v : A) = \mathit{WellFounded}.\mathit{Nat}.\mathit{fix} (\mathit{fun} (x : V) => (\mathit{val} T).\mathit{dist} r x) \mathit{fun} (v : V) (a : (y : V) \to \mathit{InvImage} (\mathit{fun} (\mathit{x1} \mathit{x2} : \mathbb{N}) => \mathit{x1} < \mathit{x2}) (\mathit{fun} (x : V) => (\mathit{val} T).\mathit{dist} r x) y v \to A) => \mathit{if} \mathit{hv} : v = r \mathit{then} \mathit{base} \mathit{else} \mathit{diff} \langle v, \mathit{hv}\rangle + a (\mathit{parent} T r \langle v, \mathit{hv}\rangle )$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.10 (Hits).**

$$\forall (V: \mathit{Type}), \forall (f: V \to V), \forall (x: V), \forall (y: V), (\mathit{Hits} V f x y : \mathit{Prop}) = \exists (m : \mathbb{N}), f^[m] x = y$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.Hits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.11 (Root Map).**

$$\forall (V: \mathit{Type}), \forall (r: V), (\mathit{RootMap} V r : \mathit{Type} (\mathit{max} 0 u)) = \{ f : V \to V  |  f r = r \land \forall (v : V), \mathit{CayleyParent}.\mathit{Hits} f v r \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.RootMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.12 (Depth).**

$$\forall (V: \mathit{Type}), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), \forall (v: V), (\mathit{depth} V r f v : \mathbb{N}) = \mathit{min} (\mathit{fun} (n : \mathbb{N}) => \mathit{Hits} f a n)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.13 (Depth hits).**

$$\forall (V: \mathit{Type}), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), \forall (v: V), (\mathit{val} f)^[\mathit{depth} r f v] v = r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_hits` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.14 (Depth min).**

$$\forall (V: \mathit{Type}), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), \forall (v: V), \forall (d: \mathbb{N}), \forall (h: (\mathit{val} f)^[d] v = r), \mathit{depth} r f v \leq d$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.15 (Depth step).**

$$\forall (V: \mathit{Type}), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), \forall (v: V), \forall (\mathit{hv}: v \neq r), \mathit{depth} r f v = \mathit{depth} r f (\mathit{val} f v) + 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.16 (Depth zero).**

$$\forall (V: \mathit{Type}), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), \forall (v: V), \mathit{depth} r f v = 0 \iff v = r$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.17 (From Tree).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (a: V), (\mathit{fromTree} V T r a : V) = \mathit{if} \mathit{hv} : v = r \mathit{then} r \mathit{else} \mathit{parent} T r \langle v, \mathit{hv}\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.fromTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.18 (From Tree child).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (v: \mathit{CayleyColors}.\mathit{Away} r), \mathit{fromTree} T r \mathit{val} v = \mathit{parent} T r v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.fromTree_child` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.19 (Hits refl).**

$$\forall (V: \mathit{Type}), \forall (f: V \to V), \forall (x: V), \mathit{CayleyParent}.\mathit{Hits} f x x$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_refl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.20 (Hits step).**

$$\forall (V: \mathit{Type}), \forall (f: V \to V), \forall (x: V), \mathit{CayleyParent}.\mathit{Hits} f x (f x)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.21 (Hits trans).**

$$\forall (V: \mathit{Type}), \forall (f: V \to V), \forall (x: V), \forall (y: V), \forall (z: V), \forall (\mathit{hxy}: \mathit{CayleyParent}.\mathit{Hits} f x y), \forall (\mathit{hyz}: \mathit{CayleyParent}.\mathit{Hits} f y z), \mathit{CayleyParent}.\mathit{Hits} f x z$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.22 (Root Map Equiv).**

$$\forall (V: \mathit{Type}), \forall (r: V), (\mathit{rootMapEquiv} V r : \mathit{CayleyProbe}.\mathit{Tree} V \equiv \mathit{CayleyParent}.\mathit{RootMap} r) = \{ \mathit{toFun} := \mathit{fun} (T : \mathit{CayleyProbe}.\mathit{Tree} V) => \langle \mathit{fromTree} T r\rangle , \mathit{invFun} := \mathit{toTree} r \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.rootMapEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.23 (To Graph).**

$$\forall (V: \mathit{Type}), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), (\mathit{toGraph} V r f : \mathit{SimpleGraph} V) = \{ \mathit{Adj} := \mathit{fun} (v w : V) => v \neq r \land \mathit{val} f v = w \lor w \neq r \land \mathit{val} f w = v \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.toGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.24 (To Tree).**

$$\forall (V: \mathit{Type}), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), (\mathit{toTree} V r f : \mathit{CayleyProbe}.\mathit{Tree} V) = \langle \mathit{toGraph} r f\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.toTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.Away`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.Hits`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.RootMap`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_hits`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_min`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_step`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.depth_zero`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edgeColorEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edgeEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.edge_orientation`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.fromTree`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.fromTree_child`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_refl`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_step`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.hits_trans`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent_spec`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.parent_unique`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.reconstruct`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.rootMapEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.toGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.toTree`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates.zero_pattern_iff`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition](TreeDecomposition.md)
