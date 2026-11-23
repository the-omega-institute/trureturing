# Exact colored Cayley-tree move-count law

## Abstract

The sequential move count has the same finite law as the number of occupied ordinary bins.

**Theorem 1.1 (Count law at every positive size).**

$$\forall (n: \mathbb{N}), \forall (k: \mathbb{N}), 0<n \implies 2 \leq k \implies \forall (K: Type), \forall (e: \operatorname{Embedding}\left(\operatorname{ZMod}\left(k\right), K\right)), \forall (P: (s: \operatorname{Colored}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(k\right)\right)) \to \operatorname{FreePolicy}\left(K, \operatorname{graph}\left(s\right)\right)), \forall (j: \mathbb{N}), \operatorname{card}\left(\operatorname{TotalNumerator}\left(e, P, j\right)\right) \cdot \operatorname{card}\left(\operatorname{Throws}\left(0, \operatorname{ZMod}\left(k\right)\right)\right) = \operatorname{frequency}\left(\operatorname{Throws}\left(0, \operatorname{ZMod}\left(k\right)\right), occupied, j\right) \cdot \operatorname{card}\left(\operatorname{SourceSample}\left(n, k\right)\right) \land 0<\operatorname{card}\left(\operatorname{SourceSample}\left(n, k\right)\right) \land 0<\operatorname{card}\left(\operatorname{Throws}\left(0, \operatorname{ZMod}\left(k\right)\right)\right) \land \operatorname{card}\left(\operatorname{Away}\left(0\right)\right) = n - 1 \land \operatorname{card}\left(\operatorname{Throw}\left(\operatorname{Fin}\left(n\right), \operatorname{ZMod}\left(k\right)\right)\right) = n \cdot k \land (\forall (b: \operatorname{Fin}\left(n\right)), \operatorname{card}\left(\operatorname{BinFiber}\left(\operatorname{some}\left(b\right)\right)\right) = 1) \land \operatorname{card}\left(\operatorname{BinFiber}\left(none\right)\right) = n \cdot \left(k - 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.native_daemon_occupancy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Élie de Panafieu, Fabien Mathieu, Maria Potop-Butucaru, and Sébastien Tixeuil (2026). *The Exact Stabilization Time of Self-Stabilizing Coloring: Mean, Variance, and Distribution*. DOI: [10.48550/arXiv.2611.17989](https://doi.org/10.48550/arXiv.2611.17989). URL: <https://arxiv.org/abs/2611.17989v1>.

*Commentary.*

The source numerator sums the weights of legal terminal histories at a given length over every rooted tree and initial coloring. The denominator is the number of uniform ranking and colored-tree samples. On the other side the numerator counts words with the given occupancy, and the denominator counts all marked words. The anchor is zero, and a bin survives a throw exactly when its mark in the additive color group is zero.

**Theorem 1.2 (Sample spaces positive).**

$$\forall (V: \mathit{Type}), [\mathit{Fintype} V] [\mathit{LinearOrder} V] \forall (k: \mathbb{N}), \forall (\mathit{hk}: 2 \leq k), \forall (\mathit{anchor}: V), 0 < \mathit{Nat}.\mathit{card} (\mathit{Equiv}.\mathit{Perm} V \times \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)) \land 0 < \mathit{Nat}.\mathit{card} (\mathit{CayleyFiniteLaw}.\mathit{Throws} \mathit{anchor} (\mathit{ZMod} k))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.sample_spaces_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.3 (Source Count).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), [\mathit{Fintype} V] [\mathit{LinearOrder} V] \forall (k: \mathbb{N}), \forall (\mathit{embed}: \mathit{ZMod} k \operatorname{embeds} K), \forall (s: \mathit{Equiv}.\mathit{Perm} V \times \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)), (\mathit{sourceCount} V K k \mathit{embed} s : \mathbb{N}) = (\mathit{rankedHistory} (\mathit{conflict} (\mathit{val} s.2.1.2) (\mathit{coe} \mathit{embed} \circ s.2.2)) s.1 \mathit{Set}.\mathit{univ}).\mathit{length}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.sourceCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.4 (Throw).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), (\mathit{Throw} V A : \mathit{Type} (\mathit{max} u w)) = V \times A$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Throw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.5 (Throws).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (A: \mathit{Type}), (\mathit{Throws} V a A : \mathit{Type} (\mathit{max} u w)) = \mathit{CayleyColors}.\mathit{Away} a \to \mathit{CayleyFiniteLaw}.\mathit{Throw} V A$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Throws` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.6 (Bin).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (a: \mathit{CayleyFiniteLaw}.\mathit{Throw} V A), (\mathit{bin} V A a : \mathit{Option} V) = \mathit{if} a.2 = 0 \mathit{then} \mathit{some} a.1 \mathit{else} \mathit{none}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Theorem 1.7 (Bin none card).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \mathit{Nat}.\mathit{card} \{ x : \mathit{CayleyFiniteLaw}.\mathit{Throw} V A  |  \mathit{bin} x = \mathit{none} \} = \mathit{Nat}.\mathit{card} V \cdot \mathit{Nat}.\mathit{card} \{ c : A  |  c \neq 0 \}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_none_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.8 (Bin none iff).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (x: \mathit{CayleyFiniteLaw}.\mathit{Throw} V A), \mathit{bin} x = \mathit{none} \iff x.2 \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_none_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.9 (Bin some card).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (v: V), \mathit{Nat}.\mathit{card} \{ x : \mathit{CayleyFiniteLaw}.\mathit{Throw} V A  |  \mathit{bin} x = \mathit{some} v \} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_some_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.10 (Bin some iff).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] \forall (x: \mathit{CayleyFiniteLaw}.\mathit{Throw} V A), \forall (v: V), \mathit{bin} x = \mathit{some} v \iff x.1 = v \land x.2 = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_some_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Theorem 1.11 (Cardinality nonzero).**

$$\forall (k: \mathbb{N}), [\mathit{NeZero} k] \mathit{Nat}.\mathit{card} \{ c : \mathit{ZMod} k  |  c \neq 0 \} = k - 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.cardinality_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed equality or implication states the law.

**Definition 1.12 (Coded Draw Equiv).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Finite} V] \forall (a: V), (\mathit{codedDrawEquiv} V A a : \mathit{CayleyFiniteLaw}.\mathit{Throws} a A \equiv (p : V \times \mathit{CayleyProbe}.\mathit{Tree} V) \times (\mathit{CayleyColors}.\mathit{Away} p.1 \to A)) = (\mathit{prodFunctions} (\mathit{CayleyColors}.\mathit{Away} a) V A).\mathit{trans} ((\mathit{Equiv}.\mathit{sigmaEquivProd} (\mathit{CayleyColors}.\mathit{Away} a \to V) (\mathit{CayleyColors}.\mathit{Away} a \to A)).\mathit{symm}.\mathit{trans} (((\mathit{rootedCode} a).\mathit{trans} (\mathit{Equiv}.\mathit{sigmaEquivProd} V (\mathit{CayleyProbe}.\mathit{Tree} V))).\mathit{sigmaCongr} \mathit{fun} (f : \mathit{CayleyColors}.\mathit{Away} a \to V) => (\mathit{codeCoordinates} a f).\mathit{arrowCongr} (\mathit{Equiv}.\mathit{refl} A)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.codedDrawEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.13 (Frequency).**

$$\forall (X: \mathit{Type}), \forall (f: X \to \mathbb{N}), \forall (j: \mathbb{N}), (\mathit{frequency} X f j : \mathbb{N}) = \mathit{Nat}.\mathit{card} \{ x : X  |  f x = j \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.frequency` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.14 (Occupied).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Fintype} V] [\mathit{Zero} A] \forall (a: V), \forall (t: \mathit{CayleyFiniteLaw}.\mathit{Throws} a A), (\mathit{occupied} V A a t : \mathbb{N}) = \mathit{filterCard} \mathit{fun} (v : V) => \exists (i : \mathit{CayleyColors}.\mathit{Away} a), \mathit{bin} (t i) = \mathit{some} v$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.occupied` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.15 (Terminal).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), [\mathit{LinearOrder} V] \forall (G: \mathit{SimpleGraph} V), \forall (\mathit{policy}: \mathit{CayleyScheduler}.\mathit{FreePolicy} G), \forall (c: V \to K), \forall (l: \mathit{List} V), (\mathit{Terminal} V K G \mathit{policy} c l : \mathit{Prop}) = \exists (\mathit{final} : V \to K), \mathit{CayleyScheduler}.\mathit{PolicyRun} G \mathit{policy} [] c l \mathit{final} \land \forall (v w : V), \neg (\mathit{conflict} G \mathit{final}).\mathit{Adj} v w$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Terminal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.16 (Total Numerator).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), [\mathit{LinearOrder} V] \forall (k: \mathbb{N}), \forall (\mathit{embed}: \mathit{ZMod} k \operatorname{embeds} K), \forall (\mathit{policy}: (s : \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)) \to \mathit{CayleyScheduler}.\mathit{FreePolicy} \mathit{val} s.1.2), \forall (j: \mathbb{N}), (\mathit{TotalNumerator} V K k \mathit{embed} \mathit{policy} j : \mathit{Type}) = (s : \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)) \times \mathit{CayleyNativeLaw}.\mathit{NativeNumerator} (\mathit{val} s.1.2) (\mathit{policy} s) (\mathit{coe} \mathit{embed} \circ s.2) j$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.TotalNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.17 (Total Equiv).**

$$\forall (V: \mathit{Type}), \forall (K: \mathit{Type}), [\mathit{Fintype} V] [\mathit{LinearOrder} V] \forall (k: \mathbb{N}), \forall (\mathit{embed}: \mathit{ZMod} k \operatorname{embeds} K), \forall (\mathit{policy}: (s : \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)) \to \mathit{CayleyScheduler}.\mathit{FreePolicy} \mathit{val} s.1.2), \forall (j: \mathbb{N}), (\mathit{totalEquiv} V K k \mathit{embed} \mathit{policy} j : \mathit{CayleyNativeLaw}.\mathit{TotalNumerator} \mathit{embed} \mathit{policy} j \equiv \{ s : \mathit{Equiv}.\mathit{Perm} V \times \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)  |  \mathit{sourceCount} \mathit{embed} s = j \}) = \mathit{let} H := \mathit{fun} (s : \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)) => \{ \mathit{rank} : \mathit{Equiv}.\mathit{Perm} V  |  \mathit{sourceCount} \mathit{embed} (\mathit{rank}, s) = j \}; (\mathit{Equiv}.\mathit{sigmaCongrRight} \mathit{fun} (s : \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)) => \mathit{conditionalEquiv} (\mathit{val} s.1.2) (\mathit{policy} s) (\mathit{coe} \mathit{embed} \circ s.2) j).\mathit{trans} (\mathit{id} \{ \mathit{toFun} := \mathit{fun} (x : (s : \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)) \times H s) => \langle (\mathit{val} x.\mathit{snd}, x.\mathit{fst})\rangle , \mathit{invFun} := \mathit{fun} (s : \{ s : \mathit{Equiv}.\mathit{Perm} V \times \mathit{CayleyReduction}.\mathit{Colored} V (\mathit{ZMod} k)  |  \mathit{sourceCount} \mathit{embed} s = j \}) => \langle (\mathit{val} s).2, \langle (\mathit{val} s).1\rangle \rangle \})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.totalEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.18 (Colored).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), (\mathit{Colored} V A : \mathit{Type} (\mathit{max} u u w)) = (V \times \mathit{CayleyProbe}.\mathit{Tree} V) \times (V \to A)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Colored` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.19 (Edge Draw).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), (\mathit{EdgeDraw} V A : \mathit{Type} (\mathit{max} u u w)) = (p : V \times \mathit{CayleyProbe}.\mathit{Tree} V) \times A \times (\mathit{val} (\mathit{val} p.2).\mathit{edgeSet} \to A)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.EdgeDraw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.20 (Parent Draw).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), (\mathit{ParentDraw} V A : \mathit{Type} (\mathit{max} u u w)) = (p : V \times \mathit{CayleyProbe}.\mathit{Tree} V) \times A \times (\mathit{CayleyColors}.\mathit{Away} p.1 \to A)$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.ParentDraw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.21 (Marked At).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Zero} A] (\mathit{markedAt} V A : \mathit{Type} (\mathit{max} u w u)) = V \times A \times \mathit{CayleyMarks}.\mathit{Marked} V A$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.markedAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.22 (Recolor Count).**

$$\forall (V: \mathit{Type}), \forall (A: \mathit{Type}), [\mathit{Fintype} V] [\mathit{LinearOrder} V] \forall (s: \mathit{Equiv}.\mathit{Perm} V \times \mathit{CayleyReduction}.\mathit{Colored} V A), (\mathit{recolorCount} V A s : \mathbb{N}) = (\mathit{rankedHistory} (\mathit{conflict} (\mathit{val} s.2.1.2) s.2.2) s.1 \mathit{Set}.\mathit{univ}).\mathit{length}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.recolorCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Colored`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.EdgeDraw`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.ParentDraw`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Terminal`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Throw`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.Throws`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.TotalNumerator`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_none_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_none_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_some_card`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.bin_some_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.cardinality_nonzero`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.codedDrawEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.frequency`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.markedAt`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.native_daemon_occupancy`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.occupied`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.recolorCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.sample_spaces_positive`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.sourceCount`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/FiniteLaw.totalEquiv`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode](CayleyCode.md)
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler](CentralScheduler.md)
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly](ForestReassembly.md)
