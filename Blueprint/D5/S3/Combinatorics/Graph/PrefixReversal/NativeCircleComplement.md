# Complete Native Circle Cut Pieces

## Abstract

A native a/b circle has complete actual cut complements, with supports exhausting its independently defined rotation-and-reversal domain.

**Theorem 1.1 (Actual Rotation Preserves the Tuple Cycle).**

$$\forall m \in \mathrm{Nat},\; \forall z \in \mathrm{Configuration}\left(m\right),\; \forall r \in \mathrm{Fin}\left(m + 1\right),\; \mathrm{configurationCycle}\left(z \cdot \mathrm{finCycle}\left(r\right)\right) = \mathrm{configurationCycle}\left(z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_configurationCycle_rotation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Right multiplication by any finCycle rotation preserves the actual tuple modulo rotations.

**Theorem 1.2 (Actual Full Reversal Reverses the Tuple Cycle).**

$$\forall m \in \mathrm{Nat},\; \forall z \in \mathrm{Configuration}\left(m\right),\; \mathrm{configurationCycle}\left(z \cdot \mathrm{a}\left(m\right)\right) = \mathrm{reverse}\left(\mathrm{configurationCycle}\left(z\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_configurationCycle_reversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Right multiplication by a reverses the actual configuration tuple cycle.

Let m be at least three and let z be a permutation of Fin(m+1). Circle(z,v) means that the actual circular tuple of v equals that of z or its whole reversal; only rotations are quotiented in the tuple. Thus Circle is specified without reference to a walk. Its coordinates are z*R^r and z*R^r*a for r in Fin(m+1), where R=ab rotates all positions by one.

**Definition 1.3 (All Actual Native Circle Coordinates).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \mathrm{Equiv}\left(\mathrm{Prod}\left(\mathrm{Fin}\left(m + 1\right), \mathrm{Bool}\right), \mathrm{CircleDomain}\left(z\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.circleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinates form a bijection onto Circle(z). Injectivity reuses the existing deletion-star coordinateEquiv at one fixed gap, rather than proving a second dihedral injection. Surjectivity comes from actual tuple rotations; the negative case applies a whole reversal first, and then uses the involution a to recover the configuration.

**Theorem 1.4 (The Complete b-Cut Complement).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{deleteEdges}\left(\mathrm{nativeABGraph}\left(m\right), \mathrm{singletonEdge}\left(z, \mathrm{rightMultiply}\left(z, \mathrm{b}\left(m\right)\right)\right)\right), z, \mathrm{rightMultiply}\left(z, \mathrm{b}\left(m\right)\right)\right),\; \mathrm{IsPath}\left(w\right) \land \left(\mathrm{length}\left(w\right) = 2 \cdot \left(m + 1\right) - 1 \land \left(\mathrm{support}\left(w\right) = \mathrm{scanl}\left(\mathrm{rightMultiply}, z, \mathrm{uWord}\left(m, m\right)\right) \land \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{mem}\left(v, \mathrm{support}\left(w\right)\right) \Leftrightarrow \mathrm{Circle}\left(z, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_b_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal H word is U_m=(ab)^m*a, with length 2(m+1)-1 and product b. Its scanl is the ordered flattened list [z*R^r,z*R^r*a] over all r in Fin(m+1). The circle-coordinate bijection makes this trace simple and exhaustive. Every step is an actual a/b edge. A simple path containing the edge between its endpoints would have length one, so the displayed long path avoids its b-cut edge and transfers to the graph with that edge deleted.

**Theorem 1.5 (The Complete a-Cut Complement).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{deleteEdges}\left(\mathrm{nativeABGraph}\left(m\right), \mathrm{singletonEdge}\left(z, \mathrm{rightMultiply}\left(z, \mathrm{a}\left(m\right)\right)\right)\right), z, \mathrm{rightMultiply}\left(z, \mathrm{a}\left(m\right)\right)\right),\; \mathrm{IsPath}\left(w\right) \land \left(\mathrm{length}\left(w\right) = 2 \cdot \left(m + 1\right) - 1 \land \left(\mathrm{support}\left(w\right) = \mathrm{cons}\left(z, \mathrm{reverse}\left(\mathrm{tail}\left(\mathrm{scanl}\left(\mathrm{rightMultiply}, z, \mathrm{uWord}\left(m, m\right)\right)\right)\right)\right) \land \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{mem}\left(v, \mathrm{support}\left(w\right)\right) \Leftrightarrow \mathrm{Circle}\left(z, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_a_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with the actual b-cut H path. Its second vertex is z*a. Reverse the path after its first a-edge, and prepend the actual b-edge from z to z*b. The support is z followed by the reverse of the H trace's tail. It is a permutation of the original complete simple support. Its endpoint is z*a, its length remains 2(m+1)-1, and simplicity again excludes the a-cut edge.

**Theorem 1.6 (Every Other Native Edge Is Retained).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \forall g \in \mathrm{Configuration}\left(m\right),\; \forall w \in \mathrm{Walk}\left(\mathrm{nativeABGraph}\left(m\right), z, \mathrm{rightMultiply}\left(z, g\right)\right),\; \left(\left(g = \mathrm{a}\left(m\right) \lor g = \mathrm{b}\left(m\right)\right) \land \left(\mathrm{IsPath}\left(w\right) \land \left(\mathrm{length}\left(w\right) = 2 \cdot \left(m + 1\right) - 1 \land \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{mem}\left(v, \mathrm{support}\left(w\right)\right) \Leftrightarrow \mathrm{Circle}\left(z, v\right)\right)\right)\right)\right) \Rightarrow \left(\forall x \in \mathrm{Configuration}\left(m\right),\; \forall h \in \mathrm{Configuration}\left(m\right),\; \left(\mathrm{Circle}\left(z, x\right) \land \left(h = \mathrm{a}\left(m\right) \lor h = \mathrm{b}\left(m\right)\right)\right) \Rightarrow \left(\mathrm{mem}\left(\mathrm{Sym2}\left(x, \mathrm{rightMultiply}\left(x, h\right)\right), \mathrm{edges}\left(w\right)\right) \Leftrightarrow \left(\neg \mathrm{Sym2}\left(x, \mathrm{rightMultiply}\left(x, h\right)\right) = \mathrm{Sym2}\left(z, \mathrm{rightMultiply}\left(z, g\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_complement_edge_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be a or b, and let w be an actual a/b path from z to z*g, of length 2(m+1)-1, whose support is exactly Circle(z). At every x in Circle(z), and for either h=a or h=b, the edge from x to x*h occurs in w exactly when it differs from the deleted endpoint edge from z to z*g. To prove this, close the actual path with that endpoint edge. Every supported vertex has two cycle neighbors, and the native a/b graph allows only x*a and x*b. These are distinct, so equality of the finite neighbor cardinalities forces both actual edges into the cycle. Removing its literal first edge leaves precisely all other native edges in the complement. This earns the retained b edges required at subsequent one-contact insertion suppliers.

**Theorem 1.7 (The Complete Complement Edge Set).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \forall g \in \mathrm{Configuration}\left(m\right),\; \forall w \in \mathrm{Walk}\left(\mathrm{nativeABGraph}\left(m\right), z, \mathrm{rightMultiply}\left(z, g\right)\right),\; \left(\left(g = \mathrm{a}\left(m\right) \lor g = \mathrm{b}\left(m\right)\right) \land \left(\mathrm{IsPath}\left(w\right) \land \left(\mathrm{length}\left(w\right) = 2 \cdot \left(m + 1\right) - 1 \land \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{mem}\left(v, \mathrm{support}\left(w\right)\right) \Leftrightarrow \mathrm{Circle}\left(z, v\right)\right)\right)\right)\right) \Rightarrow \left(\forall e \in \mathrm{Sym2Type}\left(\mathrm{Configuration}\left(m\right)\right),\; \mathrm{mem}\left(e, \mathrm{edges}\left(w\right)\right) \Leftrightarrow \left(\mathrm{NativeCircleEdge}\left(z, e\right) \land \left(\neg e = \mathrm{Sym2}\left(z, \mathrm{rightMultiply}\left(z, g\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_complement_full_edge_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any actual undirected configuration edge e, membership in the complete native complement is equivalent to NativeCircleEdge(z,e) and inequality with the literal cut. NativeCircleEdge means that e joins x to x*h for an actual x in Circle(z) and h equal to a or b. The forward direction uses the actual walk adjacency and support to earn that form; the complete native retained-edge theorem supplies both cut exclusion and the converse. This arbitrary-edge equivalence is consumed by the full T/E graft surgery inventory, including its absence direction.

**Theorem 1.8 (Both Native Edge Endpoints Remain in Their Actual Circle).**

$$\forall m \in \mathrm{Nat},\; \forall z \in \mathrm{Configuration}\left(m\right),\; \forall v \in \mathrm{Configuration}\left(m\right),\; \forall e \in \mathrm{Sym2Type}\left(\mathrm{Configuration}\left(m\right)\right),\; \left(\mathrm{NativeCircleEdge}\left(z, e\right) \land \mathrm{mem}\left(v, e\right)\right) \Rightarrow \mathrm{Circle}\left(z, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_circle_edge_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m, if e is a NativeCircleEdge(z,e), each actual configuration v belonging to the undirected edge e lies in Circle(z). The native generators a and b both reverse the actual tuple cycle: b is a whole reversal followed by an oriented rotation. Circle is closed under either action. Undirected edge membership selects one of these two actual endpoints. Complete T deleted-edge classification consumes this endpoint property to identify the unique circle owner of any alleged retained old cut.

These are complete native D-circle pieces for switching constructions. Their membership equivalences cover every configuration in the independent circle domain, with no finite search. Connecting multiple circles still requires actual connecting edges, distinct circle ownership and complete coverage of the intended larger domain.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.circleEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_a_complement`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_b_complement`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_circle_edge_endpoint`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_complement_edge_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_complement_full_edge_inventory`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_configurationCycle_reversal`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_configurationCycle_rotation`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement](../PrefixReversalZeroStarComplement.md)
