# Peaks and leaves of a native rooted tree

## Abstract

A fixed-root bijection sends peaks to leaves in cardinality.

**Theorem 1.1 (Peak and rooted-leaf counts).**

$$\forall (V: Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{LinearOrder}\left(V\right)] \forall (r: V), \forall (T: \operatorname{Tree}\left(V\right)), \operatorname{filterCard}\left(\operatorname{Peak}\left(\operatorname{graph}\left(T\right)\right)\right) = \operatorname{filterCard}\left(\operatorname{RootedLeaf}\left(\operatorname{graph}\left(\operatorname{fixedRootEquiv}\left(r\right)\left(T\right)\right), r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv_filterCard` (`✓ std3`). ∎

*Citation.* Georg Seitz (2011). *Analysis of various parameters in labelled trees and tree-like structures*. URL: <https://repositum.tuwien.ac.at/handle/20.500.12708/10695>.

*Commentary.*

A peak has no greater-labeled neighbor. A rooted leaf has no adjacent vertex farther from the root. The equivalence removes the least label, recursively replaces the attached branches, and relabels the pivot to the specified root. Seitz gives the peak-to-leaf bijection in Corollary 5.2.2 and §5.3.1.2, and de Panafieu et al. use its distributional consequence in Proposition 5.

**Definition 1.2 (Frame).**

$$\forall (V: \mathit{Type}), \forall (p: V), \mathit{Frame} V p : \mathit{Type}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Frame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

$$
\{V : \mathit{Type}\} \to \{p : V\} \to (\mathit{parts} : \mathit{Set} (\mathit{Set} V)) \to (\forall (v : V), v \neq p \iff \exists s \in \mathit{parts}, v \in s) \to (\forall (s t : \mathit{Set} V), s \in \mathit{parts} \to t \in \mathit{parts} \to \forall (v : V), v \in s \to v \in t \to s = t) \to ((s : \mathit{val} \mathit{parts}) \to \mathit{coe} s) \to \mathit{CayleyProbe}.\mathit{Frame} p
$$

**Definition 1.3 (Branches).**

$$\forall (V: \mathit{Type}), \forall (p: V), \forall (F: \mathit{CayleyProbe}.\mathit{Frame} p), (\mathit{Branches} V p F : \mathit{Type}) = (s : \mathit{val} F.\mathit{parts}) \to \mathit{CayleyProbe}.\mathit{Tree} \mathit{coe} s$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Branches` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.4 (Assemble).**

$$\forall (V: \mathit{Type}), \forall (p: V), \forall (F: \mathit{CayleyProbe}.\mathit{Frame} p), \forall (T: F.\mathit{Branches}), (\mathit{assemble} V p F T : \mathit{CayleyProbe}.\mathit{Tree} V) = \langle F.\mathit{glue} T\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.assemble` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.5 (Depth).**

$$\forall (V: \mathit{Type}), \forall (p: V), \forall (F: \mathit{CayleyProbe}.\mathit{Frame} p), \forall (T: F.\mathit{Branches}), \forall (x: V), (\mathit{depth} V p F T x : \mathbb{N}) = \mathit{if} h : x \neq p \mathit{then} (\mathit{val} (T (F.\mathit{partAt} h))).\mathit{dist} (F.\mathit{root} (F.\mathit{partAt} h)) \langle x\rangle + 1 \mathit{else} 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.depth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.6 (Glue).**

$$\forall (V: \mathit{Type}), \forall (p: V), \forall (F: \mathit{CayleyProbe}.\mathit{Frame} p), \forall (T: F.\mathit{Branches}), (\mathit{glue} V p F T : \mathit{SimpleGraph} V) = \{ \mathit{Adj} := \mathit{fun} (x y : V) => (x = p \land \exists (s : \mathit{val} F.\mathit{parts}), y = \mathit{val} (F.\mathit{root} s)) \lor (y = p \land \exists (s : \mathit{val} F.\mathit{parts}), x = \mathit{val} (F.\mathit{root} s)) \lor \exists (s : \mathit{val} F.\mathit{parts}) (\mathit{hx} : x \in \mathit{val} s) (\mathit{hy} : y \in \mathit{val} s), (\mathit{val} (T s)).\mathit{Adj} \langle x, \mathit{hx}\rangle \langle y, \mathit{hy}\rangle \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.glue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.7 (Mem part At).**

$$\forall (V: \mathit{Type}), \forall (p: V), \forall (F: \mathit{CayleyProbe}.\mathit{Frame} p), \forall (x: V), \forall (\mathit{hx}: x \neq p), x \in \mathit{val} (F.\mathit{partAt} \mathit{hx})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.mem_partAt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.8 (Part At).**

$$\forall (V: \mathit{Type}), \forall (p: V), \forall (F: \mathit{CayleyProbe}.\mathit{Frame} p), \forall (x: V), \forall (\mathit{hx}: x \neq p), (\mathit{partAt} V p F x \mathit{hx} : \mathit{val} F.\mathit{parts}) = \mathit{choose} (\mathit{fun} (s : F.\mathit{parts}) => x \in s.\mathit{val})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.partAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cover and disjointness of the parts identify the unique part containing x away from the pivot p.

**Definition 1.9 (Peak).**

$$\forall (V: \mathit{Type}), [\mathit{LT} V] \forall (G: \mathit{SimpleGraph} V), \forall (v: V), (\mathit{Peak} V G v : \mathit{Prop}) = \forall (w : V), G.\mathit{Adj} v w \to w < v$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Peak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.10 (Rooted Leaf).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (r: V), \forall (v: V), (\mathit{RootedLeaf} V G r v : \mathit{Prop}) = \neg \exists (w : V), G.\mathit{Adj} v w \land G.\mathit{dist} r v < G.\mathit{dist} r w$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.RootedLeaf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.11 (Tree).**

$$\forall (V: \mathit{Type}), (\mathit{Tree} V : \mathit{Type} (\mathit{max} 0 u)) = \{ G : \mathit{SimpleGraph} V  |  G.\mathit{IsTree} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Tree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.12 (Cut).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (p: V), (\mathit{cut} V G p : \mathit{SimpleGraph} V) = \{ \mathit{Adj} := \mathit{fun} (x y : V) => x \neq p \land y \neq p \land G.\mathit{Adj} x y \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.13 (Cut Parts).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (p: V), (\mathit{cutParts} V G p : \mathit{Set} (\mathit{Set} V)) = \{s : \mathit{Set} V | \exists (x : V), x \neq p \land s = ((\mathit{cut} G p).\mathit{connectedComponentMk} x).\mathit{supp}\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.cutParts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.14 (Decompose).**

$$\forall (V: \mathit{Type}), \forall (p: V), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), (\mathit{decompose} V p T : (F : \mathit{CayleyProbe}.\mathit{Frame} p) \times F.\mathit{Branches}) = \langle \mathit{decomposeFrame} T p, \mathit{decomposeBranches} T p\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decompose` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.15 (Decompose Equiv).**

$$\forall (V: \mathit{Type}), \forall (p: V), (\mathit{decomposeEquiv} V p : \mathit{CayleyProbe}.\mathit{Tree} V \equiv (F : \mathit{CayleyProbe}.\mathit{Frame} p) \times F.\mathit{Branches}) = \{ \mathit{toFun} := \mathit{decompose} p, \mathit{invFun} := \mathit{fun} (a : (F : \mathit{CayleyProbe}.\mathit{Frame} p) \times F.\mathit{Branches}) => \mathit{CayleyProbe}.\mathit{Frame}.\mathit{assemble} a.\mathit{snd} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decomposeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.16 (Decompose Frame).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (p: V), (\mathit{decomposeFrame} V T p : \mathit{CayleyProbe}.\mathit{Frame} p) = \{ \mathit{parts} := \mathit{cutParts} (\mathit{val} T) p, \mathit{cover} :=, \mathit{separate} :=, \mathit{root} := \mathit{fun} (s : \mathit{val} (\mathit{cutParts} (\mathit{val} T) p)) => \langle h.\mathit{choose}\rangle \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decomposeFrame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.17 (Filter Card).**

$$\forall (V: \mathit{Type}), [\mathit{Fintype} V] \forall (p: V \to \mathit{Prop}), (\mathit{filterCard} V p : \mathbb{N}) = (\mathit{Finset}.\mathit{filter} p \mathit{Finset}.\mathit{univ}).\mathit{card}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.filterCard` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.18 (Filter Card eq nat Card).**

$$\forall (V: \mathit{Type}), [\mathit{Fintype} V] \forall (P: V \to \mathit{Prop}), \mathit{filterCard} P = \mathit{Nat}.\mathit{card} \{ x : V  |  P x \}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.filterCard_eq_natCard` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.19 (Fixed Root Equiv).**

$$\forall (V: \mathit{Type}), [\mathit{Finite} V] [\mathit{LinearOrder} V] \forall (r: V), (\mathit{fixedRootEquiv} V r : \mathit{CayleyProbe}.\mathit{Tree} V \equiv \mathit{CayleyProbe}.\mathit{Tree} V) = \mathit{val} (\mathit{fixedRootEquivSized} (\mathit{Nat}.\mathit{card} V) V r)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.20 (Relabel Equiv).**

$$\forall (V: \mathit{Type}), \forall (e: V \equiv V), (\mathit{relabelEquiv} V e : \mathit{CayleyProbe}.\mathit{Tree} V \equiv \mathit{CayleyProbe}.\mathit{Tree} V) = \{ \mathit{toFun} := \mathit{relabelTree} e, \mathit{invFun} := \mathit{relabelTree} e.\mathit{symm} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.relabelEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.21 (Relabel Tree).**

$$\forall (V: \mathit{Type}), \forall (e: V \equiv V), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), (\mathit{relabelTree} V e T : \mathit{CayleyProbe}.\mathit{Tree} V) = \langle \mathit{SimpleGraph}.\mathit{comap} \mathit{coe} e.\mathit{symm} \mathit{val} T\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.relabelTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.22 (Shorter Neighbor).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{hG}: G.\mathit{IsTree}), \forall (r: V), \forall (v: V), \forall (\mathit{hv}: v \neq r), \exists ! w : V, G.\mathit{Adj} v w \land G.\mathit{dist} r w < G.\mathit{dist} r v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.shorterNeighbor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.23 (Tree of depth).**

$$\forall (V: \mathit{Type}), \forall (G: \mathit{SimpleGraph} V), \forall (r: V), \forall (d: V \to \mathbb{N}), \forall (\mathit{zero}: \forall (v : V), d v = 0 \iff v = r), \forall (\mathit{step}: \forall (v w : V), G.\mathit{Adj} v w \to d v = d w + 1 \lor d w = d v + 1), \forall (\mathit{parent}: \forall (v : V), v \neq r \to \exists ! w : V, G.\mathit{Adj} v w \land d w < d v), G.\mathit{IsTree} \land \forall (v : V), G.\mathit{dist} r v = d v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.tree_of_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Branches`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Frame`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Peak`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.RootedLeaf`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.Tree`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.assemble`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.cut`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.cutParts`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decompose`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decomposeEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.decomposeFrame`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.depth`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.filterCard`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.filterCard_eq_natCard`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv_filterCard`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.glue`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.mem_partAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.partAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.relabelEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.relabelTree`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.shorterNeighbor`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.tree_of_depth`
