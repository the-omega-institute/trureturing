# A Cayley code preserving targets

## Abstract

Cutting the cyclic vertices at an anchor transforms a target function into a rooted tree without changing its target multiset.

**Theorem 1.1 (The code preserves every target).**

$$\forall (V: Type), [\operatorname{Finite}\left(V\right)] \forall (a: V), \forall (f: \operatorname{Away}\left(V, a\right) \to V), \forall (i: \operatorname{Away}\left(V, a\right)), \operatorname{parent}\left(\operatorname{snd}\left(\operatorname{rootedCode}\left(a\right)\left(f\right)\right), \operatorname{fst}\left(\operatorname{rootedCode}\left(a\right)\left(f\right)\right), \operatorname{codeCoordinates}\left(a, f\right)\left(i\right)\right) = f\left(i\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode_targets` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The code sends a function on the vertices other than the anchor to a rooted tree. It retains the arcs outside the cyclic core and replaces the core cycles by an anchor-first path to the root. A coordinate equivalence matches the original domain to the non-root vertices, including when the core is a singleton.

**Definition 1.2 (Anchored).**

$$\forall (V: \mathit{Type}), \forall (a: V), (\mathit{Anchored} V a : \mathit{Type} (\mathit{max} 0 u)) = \{ f : V \to V  |  f a = a \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Anchored` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.3 (Core Away).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), \forall (p: \mathit{val} F.\mathit{core}), (\mathit{CoreAway} V a F p : \mathit{Type} (\mathit{max} 0 u)) = \{ x : \mathit{val} F.\mathit{core}  |  x \neq p \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.CoreAway` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.4 (Fixed Perm).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), (\mathit{FixedPerm} V a F : \mathit{Type} (\mathit{max} 0 u)) = \{ e : \mathit{Equiv}.\mathit{Perm} \mathit{val} F.\mathit{core}  |  e F.\mathit{anchor} = F.\mathit{anchor} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.FixedPerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.5 (Frame).**

$$\forall (V: \mathit{Type}), \forall (a: V), \mathit{Frame} V a : \mathit{Type}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Frame` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

$$
\{V : \mathit{Type}\} \to \{a : V\} \to (\mathit{core} : \mathit{Set} V) \to a \in \mathit{core} \to (\mathit{outside} : V \to V) \to (\forall x \in \mathit{core}, \mathit{outside} x = x) \to (\forall (x : V), \exists (n : \mathbb{N}), \mathit{outside}^[n] x \in \mathit{core}) \to \mathit{CayleyCore}.\mathit{Frame} a
$$

**Definition 1.6 (Anchor).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), (\mathit{anchor} V a F : \mathit{val} F.\mathit{core}) = a \mathit{asSubtype} F.\mathit{core}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.anchor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.7 (Of Function).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (f: V \to V), \forall (C: \mathit{Set} V), \forall (\mathit{ha}: a \in C), \forall (h: \forall (x : V), \exists (n : \mathbb{N}), f^[n] x \in C), (\mathit{ofFunction} V a f C \mathit{ha} h : \mathit{CayleyCore}.\mathit{Frame} a) = \mathit{let} g := \mathit{fun} (x : V) => \mathit{if} x \in C \mathit{then} x \mathit{else} f x; \{ \mathit{core} := C, \mathit{anchor}\mathrm{anonymous}\mathit{mem} := \mathit{ha}, \mathit{outside} := g \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.ofFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.8 (Patch).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), \forall (g: \mathit{val} F.\mathit{core} \to \mathit{val} F.\mathit{core}), \forall (x: V), (\mathit{patch} V a F g x : V) = \mathit{if} \mathit{hx} : x \in F.\mathit{core} \mathit{then} \mathit{val} (g \langle x, \mathit{hx}\rangle ) \mathit{else} F.\mathit{outside} x$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.patch` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.9 (Orders Of Length).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), \forall (m: \mathbb{N}), (\mathit{OrdersOfLength} V a F m : \mathit{Type} (\mathit{max} 0 u)) = \{ e : \mathit{Fin} (m + 1) \equiv \mathit{val} F.\mathit{core}  |  e 0 = F.\mathit{anchor} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.OrdersOfLength` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.10 (Outside).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), (\mathit{Outside} V a F : \mathit{Type} (\mathit{max} 0 u)) = \{ x : V  |  x \neg \in F.\mathit{core} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Outside` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.11 (Path Data).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), (\mathit{PathData} V a F : \mathit{Type} (\mathit{max} 0 u)) = (m : \mathbb{N}) \times \{ e : \mathit{Fin} (m + 1) \equiv \mathit{val} F.\mathit{core}  |  e 0 = F.\mathit{anchor} \}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.PathData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.12 (Code Coordinates).**

$$\forall (V: \mathit{Type}), [\mathit{Finite} V] \forall (a: V), \forall (f: \mathit{CayleyColors}.\mathit{Away} a \to V), (\mathit{codeCoordinates} V a f : \mathit{CayleyColors}.\mathit{Away} a \equiv \mathit{CayleyColors}.\mathit{Away} ((\mathit{rootedCode} a) f).\mathit{fst}) = \mathit{have} d := (\mathit{cyclicEquiv} a) ((\mathit{extendAnchor} a) f); \mathit{matchedCoordinates} d.\mathit{snd} ((\mathit{permPathEquiv} d.\mathit{fst}) d.\mathit{snd})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.codeCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.13 (From Inside).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), \forall (p: \mathit{val} F.\mathit{core}), \forall (x: \mathit{CayleyCore}.\mathit{CoreAway} p), (\mathit{fromInside} V a F p x : \mathit{CayleyColors}.\mathit{Away} \mathit{val} p) = \langle \mathit{coe} x\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.fromInside` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.14 (From Outside).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), \forall (p: \mathit{val} F.\mathit{core}), \forall (x: \mathit{CayleyCore}.\mathit{Outside} F), (\mathit{fromOutside} V a F p x : \mathit{CayleyColors}.\mathit{Away} \mathit{val} p) = \langle \mathit{val} x\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.fromOutside` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.15 (Index Before Last).**

$$\forall (m: \mathbb{N}), (\mathit{indexBeforeLast} m : \mathit{Fin} m \equiv \{ i : \mathit{Fin} (m + 1)  |  i \neq \mathit{Fin}.\mathit{last} m \}) = \mathit{let} f := \mathit{fun} (i : \mathit{Fin} m) => \langle i.\mathit{castSucc}\rangle ; \mathit{Equiv}.\mathit{ofBijective} f$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.indexBeforeLast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.16 (Orbit Core).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), (\mathit{orbitCore} V a r f : \mathit{Set} V) = \{x : V | \mathit{CayleyParent}.\mathit{Hits} (\mathit{val} f) a x\}$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.orbitCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.17 (Orbit Equiv).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (r: V), \forall (f: \mathit{CayleyParent}.\mathit{RootMap} r), (\mathit{orbitEquiv} V a r f : \mathit{Fin} (\mathit{depth} r f a + 1) \equiv \mathit{val} (\mathit{orbitCore} a f)) = \mathit{Equiv}.\mathit{ofBijective} (\mathit{fun} (i : \mathit{Fin} (\mathit{depth} r f a + 1)) => \langle (\mathit{val} f)^[\mathit{val} i] a\rangle )$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.orbitEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.18 (Path Join).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (d: (F : \mathit{CayleyCore}.\mathit{Frame} a) \times \mathit{CayleyCore}.\mathit{PathData} F), (\mathit{pathJoin} V a d : (r : V) \times \mathit{CayleyParent}.\mathit{RootMap} r) = \mathit{Sigma}.\mathit{casesOn} d \mathit{fun} (F : \mathit{CayleyCore}.\mathit{Frame} a) (p : \mathit{CayleyCore}.\mathit{PathData} F) => \mathit{let} r := \mathit{pathRoot} p; \mathit{let} f := F.\mathit{patch} (\mathit{pathSelf} p); \langle \mathit{val} r, \langle f\rangle \rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathJoin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.19 (Path Root).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), \forall (p: \mathit{CayleyCore}.\mathit{PathData} F), (\mathit{pathRoot} V a F p : \mathit{val} F.\mathit{core}) = \mathit{val} p.\mathit{snd} (\mathit{Fin}.\mathit{last} p.\mathit{fst})$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.20 (Path Self).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (F: \mathit{CayleyCore}.\mathit{Frame} a), \forall (p: \mathit{CayleyCore}.\mathit{PathData} F), \forall (x: \mathit{val} F.\mathit{core}), (\mathit{pathSelf} V a F p x : \mathit{val} F.\mathit{core}) = \mathit{val} p.\mathit{snd} (\mathit{successor} p.\mathit{fst} ((\mathit{val} p.\mathit{snd}).\mathit{symm} x))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathSelf` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.21 (Path Split).**

$$\forall (V: \mathit{Type}), \forall (a: V), \forall (d: (r : V) \times \mathit{CayleyParent}.\mathit{RootMap} r), (\mathit{pathSplit} V a d : (F : \mathit{CayleyCore}.\mathit{Frame} a) \times \mathit{CayleyCore}.\mathit{PathData} F) = \mathit{let} F := \mathit{CayleyCore}.\mathit{Frame}.\mathit{ofFunction} (\mathit{val} d.\mathit{snd}) (\mathit{orbitCore} a d.\mathit{snd}); \langle F, \langle \mathit{depth} d.\mathit{fst} d.\mathit{snd} a, \langle \mathit{orbitEquiv} a d.\mathit{snd}\rangle \rangle \rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.22 (Rooted Code).**

$$\forall (V: \mathit{Type}), [\mathit{Finite} V] \forall (a: V), (\mathit{rootedCode} V a : (\mathit{CayleyColors}.\mathit{Away} a \to V) \equiv (\mathrm{anonymous} : V) \times \mathit{CayleyProbe}.\mathit{Tree} V) = (\mathit{extendAnchor} a).\mathit{trans} ((\mathit{cyclicEquiv} a).\mathit{trans} ((\mathit{Equiv}.\mathit{sigmaCongrRight} \mathit{permPathEquiv}).\mathit{trans} ((\mathit{pathEquiv} a).\mathit{symm}.\mathit{trans} \mathit{nativeRootedEquiv}.\mathit{symm})))$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

**Definition 1.23 (Successor).**

$$\forall (m: \mathbb{N}), \forall (i: \mathit{Fin} (m + 1)), (\mathit{successor} m i : \mathit{Fin} (m + 1)) = \langle \mathit{min} (\mathit{val} i + 1) m\rangle$$

*Formalization.* `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.successor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed formula specifies the construction.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Anchored`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.CoreAway`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.FixedPerm`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Frame`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.OrdersOfLength`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.Outside`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.PathData`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.anchor`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.codeCoordinates`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.fromInside`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.fromOutside`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.indexBeforeLast`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.ofFunction`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.orbitCore`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.orbitEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.patch`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathJoin`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathRoot`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathSelf`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.pathSplit`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.rootedCode_targets`
- Truth anchor: `D5/S3/Combinatorics/Graph/CayleyColoring/CayleyCode.successor`
- Dependency: [D5/S3/Combinatorics/Graph/CayleyColoring/RootedCoordinates](RootedCoordinates.md)
