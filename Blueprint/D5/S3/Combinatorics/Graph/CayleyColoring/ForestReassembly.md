# Peak transport in a retained forest

## Abstract

Reassembling the conflict components turns peaks into vertices without retained children.

**Theorem 1.1 (Count transport for marked trees).**

$$\forall (V: Type), [\operatorname{Fintype}\left(V\right)] [\operatorname{LinearOrder}\left(V\right)] \forall (r: V), \forall (S: \operatorname{ForestSample}\left(V\right)), \operatorname{card}\left(\operatorname{PeakSet}\left(\operatorname{retained}\left(S\right)\right)\right) = \operatorname{card}\left(\operatorname{NoRetainedChildSet}\left(\operatorname{tree}\left(\operatorname{forestEquiv}\left(r\right)\left(S\right)\right), \operatorname{retained}\left(\operatorname{forestEquiv}\left(r\right)\left(S\right)\right), r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv_peaks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

The sample consists of a tree and a spanning subgraph obtained by retaining some edges. Each component is rooted at its entry vertex on paths from the ambient root. Replace its tree by the fixed-root image and leave all intercomponent edges in place. This relates its original peak count to the number of vertices with no retained child in the new rooted tree.

**Definition 1.2 (Family).**

$$\forall (V: \mathit{Type}), \forall (P: \mathit{Set} (\mathit{Set} V)), (\mathit{Family} V P : \mathit{Type}) = (s : \mathit{val} P) \to \mathit{CayleyProbe}.\mathit{Tree} \mathit{coe} s$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Family` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.3 (No Retained Child).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (H: \mathit{SimpleGraph} V), \forall (r: V), \forall (v: V), (\mathit{NoRetainedChild} V T H r v : \mathit{Prop}) = \neg \exists (w : V), H.\mathit{Adj} v w \land (\mathit{val} T).\mathit{dist} r v < (\mathit{val} T).\mathit{dist} r w$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.NoRetainedChild` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.4 (Sample).**

$$\forall (V: \mathit{Type}), (\mathit{Sample} V : \mathit{Type} (\mathit{max} 0 u)) = \{ s : \mathit{CayleyProbe}.\mathit{Tree} V \times \mathit{SimpleGraph} V  |  s.2 \leq \mathit{val} s.1 \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Sample` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.5 (Block).**

$$\forall (V: \mathit{Type}), \forall (P: \mathit{Set} (\mathit{Set} V)), \forall (U: \mathit{CayleyForest}.\mathit{Family} P), \forall (s: \mathit{val} P), (\mathit{block} V P U s : \mathit{SimpleGraph} V) = \mathit{SimpleGraph}.\mathit{map} \mathit{coe} (\mathit{Function}.\mathit{Embedding}.\mathit{subtype} \mathit{fun} (x : V) => x \in \mathit{val} s) \mathit{val} (U s)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.6 (Entry).**

$$\forall (V: \mathit{Type}), [\mathit{Finite} V] \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (H: \mathit{SimpleGraph} V), \forall (s: \mathit{Set} V), \forall (\mathit{hs}: s \in \mathit{parts} H), (\mathit{entry} V T r H s \mathit{hs} : \mathit{val} s) = \mathit{argmin} (\mathit{fun} (v : s) => T.\mathit{val}.\mathit{dist} r v.\mathit{val})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.entry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entry is an element of the retained component that minimizes its distance from the original root.

**Definition 1.7 (Forest Equiv).**

$$\forall (V: \mathit{Type}), [\mathit{Finite} V] [\mathit{LinearOrder} V] \forall (r: V), (\mathit{forestEquiv} V r : \mathit{CayleyForest}.\mathit{Sample} V \equiv \mathit{CayleyForest}.\mathit{Sample} V) = \{ \mathit{toFun} := \mathit{fun} (S : \mathit{CayleyForest}.\mathit{Sample} V) => \mathit{transform} r S \mathit{false}, \mathit{invFun} := \mathit{fun} (S : \mathit{CayleyForest}.\mathit{Sample} V) => \mathit{transform} r S \mathit{true} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.8 (Local Tree).**

$$\forall (V: \mathit{Type}), \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (H: \mathit{SimpleGraph} V), \forall (h: H \leq \mathit{val} T), \forall (s: \mathit{Set} V), \forall (\mathit{hs}: s \in \mathit{parts} H), (\mathit{localTree} V T H h s \mathit{hs} : \mathit{CayleyProbe}.\mathit{Tree} \mathit{val} s) = \mathit{restrictTree} T H s$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.localTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.9 (Parts).**

$$\forall (V: \mathit{Type}), \forall (H: \mathit{SimpleGraph} V), (\mathit{parts} V H : \mathit{Set} (\mathit{Set} V)) = \mathit{Set}.\mathit{range} \mathit{fun} (c : H.\mathit{ConnectedComponent}) => c.\mathit{supp}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.parts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.10 (Replace).**

$$\forall (V: \mathit{Type}), [\mathit{Finite} V] \forall (S: \mathit{CayleyForest}.\mathit{Sample} V), \forall (U: \mathit{CayleyForest}.\mathit{Family} (\mathit{parts} (\mathit{val} S).2)), (\mathit{replace} V S U : \mathit{CayleyForest}.\mathit{Sample} V) = \mathit{let} T := (\mathit{val} S).1; \mathit{let} H := (\mathit{val} S).2; \mathit{let} C := \mathit{val} T \setminus H; \mathit{let} \mathit{Hnew} := \mathit{unionGraph} U; \langle (\langle C \operatorname{sup} \mathit{Hnew}, \mathit{ht}\rangle , \mathit{Hnew})\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.replace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.11 (Union Graph).**

$$\forall (V: \mathit{Type}), \forall (P: \mathit{Set} (\mathit{Set} V)), \forall (U: \mathit{CayleyForest}.\mathit{Family} P), (\mathit{unionGraph} V P U : \mathit{SimpleGraph} V) = \operatorname{iSup} (s : \mathit{val} P), \mathit{block} U s$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.unionGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.12 (Deleted).**

$$\forall (V: \mathit{Type}), \forall (S: \mathit{CayleyForest}.\mathit{Sample} V), (\mathit{Deleted} V S : \mathit{Type} (\mathit{max} 0 u)) = \{ e : \mathit{Sym2} V  |  e \in (\mathit{val} (\mathit{val} S).1).\mathit{edgeSet} \land e \neg \in (\mathit{val} S).2.\mathit{edgeSet} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Deleted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.13 (Has Target).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (d: \mathit{CayleyColors}.\mathit{Away} r \to A), \forall (w: V), (\mathit{HasTarget} V A T r d w : \mathit{Prop}) = \exists (v : \mathit{CayleyColors}.\mathit{Away} r), \mathit{parent} T r v = w \land d v = 0$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.HasTarget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.14 (Marked).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] (\mathit{Marked} V A : \mathit{Type} (\mathit{max} u u w)) = (S : \mathit{CayleyForest}.\mathit{Sample} V) \times (\mathit{CayleyMarks}.\mathit{Deleted} S \to \{ x : A  |  x \neq 0 \})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Marked` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.15 (Conflict retained).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{AddGroup} A] \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (c: V \to A), \mathit{retained} T ((\mathit{edgeColorEquiv} T r) c).2 = \mathit{conflict} (\mathit{val} T) c$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.conflict_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.16 (Fill).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (x: \mathit{CayleyMarks}.\mathit{Marked} V A), \forall (e: \mathit{val} (\mathit{val} (\mathit{val} x.\mathit{fst}).1).\mathit{edgeSet}), (\mathit{fill} V A x e : A) = \mathit{if} h : \mathit{val} e \in (\mathit{val} x.\mathit{fst}).2.\mathit{edgeSet} \mathit{then} 0 \mathit{else} \mathit{val} (x.\mathit{snd} \langle \mathit{val} e\rangle )$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.fill` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.17 (Join).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (x: \mathit{CayleyMarks}.\mathit{Marked} V A), (\mathit{join} V A x : (T : \mathit{CayleyProbe}.\mathit{Tree} V) \times (\mathit{val} (\mathit{val} T).\mathit{edgeSet} \to A)) = \langle (\mathit{val} x.\mathit{fst}).1, \mathit{fill} x\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.join` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.18 (Join retained).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (x: \mathit{CayleyMarks}.\mathit{Marked} V A), \mathit{retained} (\mathit{val} x.\mathit{fst}).1 (\mathit{fill} x) = (\mathit{val} x.\mathit{fst}).2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.join_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.19 (Marked Equiv).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] (\mathit{markedEquiv} V A : (T : \mathit{CayleyProbe}.\mathit{Tree} V) \times (\mathit{val} (\mathit{val} T).\mathit{edgeSet} \to A) \equiv \mathit{CayleyMarks}.\mathit{Marked} V A) = \{ \mathit{toFun} := \mathit{split}, \mathit{invFun} := \mathit{join} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.markedEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.20 (Marked Forest Equiv).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] [\mathit{Finite} V] [\mathit{LinearOrder} V] \forall (r: V), (\mathit{markedForestEquiv} V A r : \mathit{CayleyMarks}.\mathit{Marked} V A \equiv \mathit{CayleyMarks}.\mathit{Marked} V A) = (\mathit{forestEquiv} r).\mathit{sigmaCongr} \mathit{fun} (S : \mathit{CayleyForest}.\mathit{Sample} V) => \mathit{have} e := \mathit{Set}.\mathit{equivOfEq}; ((\mathit{deletedEquiv} S).\mathit{trans} (e.\mathit{trans} (\mathit{deletedEquiv} ((\mathit{forestEquiv} r) S)).\mathit{symm})).\mathit{arrowCongr} (\mathit{Equiv}.\mathit{refl} \{ x : A  |  x \neq 0 \})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.markedForestEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.21 (Retained).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (d: \mathit{val} (\mathit{val} T).\mathit{edgeSet} \to A), (\mathit{retained} V A T d : \mathit{SimpleGraph} V) = \mathit{SimpleGraph}.\mathit{fromEdgeSet} \{e : \mathit{Sym2} V | \exists (h : e \in (\mathit{val} T).\mathit{edgeSet}), d \langle e, h\rangle = 0\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.22 (Retained child iff).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (r: V), \forall (d: \mathit{val} (\mathit{val} T).\mathit{edgeSet} \to A), \forall (w: V), (\exists (v : V), (\mathit{retained} T d).\mathit{Adj} w v \land (\mathit{val} T).\mathit{dist} r w < (\mathit{val} T).\mathit{dist} r v) \iff \mathit{CayleyMarks}.\mathit{HasTarget} T r (d \circ \mathit{coe} (\mathit{edgeEquiv} T r)) w$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained_child_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.23 (Retained le).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (T: \mathit{CayleyProbe}.\mathit{Tree} V), \forall (d: \mathit{val} (\mathit{val} T).\mathit{edgeSet} \to A), \mathit{retained} T d \leq \mathit{val} T$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.24 (Split).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (x: (T : \mathit{CayleyProbe}.\mathit{Tree} V) \times (\mathit{val} (\mathit{val} T).\mathit{edgeSet} \to A)), (\mathit{split} V A x : \mathit{CayleyMarks}.\mathit{Marked} V A) = \mathit{let} H := \mathit{retained} x.\mathit{fst} x.\mathit{snd}; \langle \langle (x.\mathit{fst}, H)\rangle , \mathit{fun} (e : \mathit{CayleyMarks}.\mathit{Deleted} \langle (x.\mathit{fst}, H)\rangle ) => \langle x.\mathit{snd} \langle \mathit{val} e, \mathit{he}\rangle \rangle \rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.split` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Deleted`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Family`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.HasTarget`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Marked`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.NoRetainedChild`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.Sample`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.block`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.conflict_retained`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.entry`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.fill`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv_peaks`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.join`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.join_retained`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.localTree`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.markedEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.markedForestEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.parts`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.replace`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained_child_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.retained_le`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.split`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.unionGraph`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler](CentralScheduler.md)
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates](RootedCoordinates.md)
