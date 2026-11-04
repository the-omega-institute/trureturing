# Finite matching networks and series contraction

## Abstract

Explicit contraction of matching networks preserves their actual connected components.

A matching on V is a fixed-point-free involution mate:V to V. Component(r) is the quotient by the reflexive, symmetric and transitive closure of the edge relation r. Parallel edges with different colors remain allowed. Coloring(r,C) consists of functions V to C constant along each r-edge. Types and relations retain their independent universes; FiniteType means an arbitrary finite type, including the empty type.

**Definition 1.1 (Series contraction by actual paths).**

$$\forall V \in Type,\; \forall W \in Type,\; \forall r \in \operatorname{Relation}\left(V\right),\; \forall s \in \operatorname{Relation}\left(W\right),\; \forall f \in \operatorname{Maps}\left(V, W\right),\; \forall g \in \operatorname{Maps}\left(W, V\right),\; \left(\left(\forall y \in W,\; \operatorname{f}\left(\operatorname{g}\left(y\right)\right) = y\right) \land \left(\left(\forall x \in V,\; \forall y \in V,\; \operatorname{r}\left(x, y\right) \Rightarrow \operatorname{EqvGen}\left(s, \operatorname{f}\left(x\right), \operatorname{f}\left(y\right)\right)\right) \land \left(\left(\forall x \in W,\; \forall y \in W,\; \operatorname{s}\left(x, y\right) \Rightarrow \operatorname{EqvGen}\left(r, \operatorname{g}\left(x\right), \operatorname{g}\left(y\right)\right)\right) \land \left(\forall x \in V,\; \operatorname{EqvGen}\left(r, x, \operatorname{g}\left(\operatorname{f}\left(x\right)\right)\right)\right)\right)\right)\right) \Rightarrow \operatorname{Equiv}\left(\operatorname{Component}\left(r\right), \operatorname{Component}\left(s\right)\right)$$

*Formalization.* `D5/S3/Topology/FiniteMatchingClosure.contractionEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map f retracts onto g: f(g(y))=y. Each source edge maps to a target path, each target edge lifts to a source path, and every source vertex is connected to g(f(x)). The induced quotient maps are inverse. No component count or matching identity is assumed.

**Theorem 1.2 (Suppressing the overlay wires).**

$$\forall V \in Type,\; \forall s \in \operatorname{Maps}\left(V, V\right),\; \forall t \in \operatorname{Maps}\left(V, V\right),\; \operatorname{card}\left(\operatorname{Component}\left(\operatorname{overlayStep}\left(s, t\right)\right)\right) = \operatorname{card}\left(\operatorname{Component}\left(\operatorname{twoStep}\left(s, t\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingClosure.overlay_component_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OverlayStep has two copies of V, the s-edges in the first copy, the t-edges in the second, and wires joining equal labels across copies. TwoStep has y=s(x) or y=t(x). The contraction uses Sum.elim(id,id) and the first inclusion, so the component equivalence holds even without finiteness or involutivity. Here card is Nat.card; no finite-cardinality interpretation is asserted for an infinite component type.

**Theorem 1.3 (One independent color per component).**

$$\forall V \in FiniteType,\; \forall C \in Type,\; \forall r \in \operatorname{Relation}\left(V\right),\; \operatorname{card}\left(\operatorname{Coloring}\left(r, C\right)\right) = \operatorname{power}\left(\operatorname{card}\left(C\right), \operatorname{card}\left(\operatorname{Component}\left(r\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/FiniteMatchingClosure.coloring_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Quotient lifting identifies edge-constant functions with arbitrary functions on Component(r). Finite V makes its component quotient finite; C remains arbitrary. The equation uses Nat.card, including its infinite-type convention.

Boundary(N) is Bool times Fin N, with false the top and true the bottom. The identity matching reverses Bool. For j+1<N, cupcapMatching pairs positions j and j+1 separately on each boundary and reverses Bool at every other position. Its involutivity and absence of fixed points hold for every valid index. GluingVertex(N) has three levels; upper and lower embed the two matching boundaries, and outer selects levels zero and two. InternalComponent consists exactly of quotient components meeting no outer vertex. These are all pairings, without a planarity or faithfulness assertion.

## References

- Truth anchor: `D5/S3/Topology/FiniteMatchingClosure.coloring_card`
- Truth anchor: `D5/S3/Topology/FiniteMatchingClosure.contractionEquiv`
- Truth anchor: `D5/S3/Topology/FiniteMatchingClosure.overlay_component_card`
