# Complete Native Circle Cut Pieces

## Abstract

A native a/b circle has complete actual cut complements, with supports exhausting its independently defined rotation-and-reversal domain.

Let m be at least three and let z be a permutation of Fin(m+1). Circle(z,v) means that the actual circular tuple of v equals that of z or its whole reversal; only rotations are quotiented in the tuple. Thus Circle is specified without reference to a walk. Its coordinates are z*R^r and z*R^r*a for r in Fin(m+1), where R=ab rotates all positions by one.

**Definition 1.1 (All Actual Native Circle Coordinates).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \mathrm{Equiv}\left(\mathrm{Prod}\left(\mathrm{Fin}\left(m + 1\right), \mathrm{Bool}\right), \mathrm{CircleDomain}\left(z\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.circleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinates form a bijection onto Circle(z). Injectivity reuses the existing deletion-star coordinateEquiv at one fixed gap, rather than proving a second dihedral injection. Surjectivity comes from actual tuple rotations; the negative case applies a whole reversal first, and then uses the involution a to recover the configuration.

**Theorem 1.2 (The Complete b-Cut Complement).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{deleteEdges}\left(\mathrm{nativeABGraph}\left(m\right), \mathrm{singletonEdge}\left(z, \mathrm{rightMultiply}\left(z, \mathrm{b}\left(m\right)\right)\right)\right), z, \mathrm{rightMultiply}\left(z, \mathrm{b}\left(m\right)\right)\right),\; \mathrm{IsPath}\left(w\right) \land \left(\mathrm{length}\left(w\right) = 2 \cdot \left(m + 1\right) - 1 \land \left(\mathrm{support}\left(w\right) = \mathrm{scanl}\left(\mathrm{rightMultiply}, z, \mathrm{uWord}\left(m, m\right)\right) \land \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{mem}\left(v, \mathrm{support}\left(w\right)\right) \Leftrightarrow \mathrm{Circle}\left(z, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_b_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal H word is U_m=(ab)^m*a, with length 2(m+1)-1 and product b. Its scanl is the ordered flattened list [z*R^r,z*R^r*a] over all r in Fin(m+1). The circle-coordinate bijection makes this trace simple and exhaustive. Every step is an actual a/b edge. A simple path containing the edge between its endpoints would have length one, so the displayed long path avoids its b-cut edge and transfers to the graph with that edge deleted.

**Theorem 1.3 (The Complete a-Cut Complement).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\forall z \in \mathrm{Configuration}\left(m\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{deleteEdges}\left(\mathrm{nativeABGraph}\left(m\right), \mathrm{singletonEdge}\left(z, \mathrm{rightMultiply}\left(z, \mathrm{a}\left(m\right)\right)\right)\right), z, \mathrm{rightMultiply}\left(z, \mathrm{a}\left(m\right)\right)\right),\; \mathrm{IsPath}\left(w\right) \land \left(\mathrm{length}\left(w\right) = 2 \cdot \left(m + 1\right) - 1 \land \left(\mathrm{support}\left(w\right) = \mathrm{cons}\left(z, \mathrm{reverse}\left(\mathrm{tail}\left(\mathrm{scanl}\left(\mathrm{rightMultiply}, z, \mathrm{uWord}\left(m, m\right)\right)\right)\right)\right) \land \left(\forall v \in \mathrm{Configuration}\left(m\right),\; \mathrm{mem}\left(v, \mathrm{support}\left(w\right)\right) \Leftrightarrow \mathrm{Circle}\left(z, v\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_a_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start with the actual b-cut H path. Its second vertex is z*a. Reverse the path after its first a-edge, and prepend the actual b-edge from z to z*b. The support is z followed by the reverse of the H trace's tail. It is a permutation of the original complete simple support. Its endpoint is z*a, its length remains 2(m+1)-1, and simplicity again excludes the a-cut edge.

These are complete native D-circle pieces for switching constructions. Their membership equivalences cover every configuration in the independent circle domain, with no finite search. Connecting multiple circles still requires actual connecting edges, distinct circle ownership and complete coverage of the intended larger domain.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.circleEquiv`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_a_complement`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeCircleComplement.native_b_complement`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement](../PrefixReversalZeroStarComplement.md)
