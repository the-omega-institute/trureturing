# Reciprocal fibers and actual link components

## Abstract

Let H be a finite family of subsets of a finite vertex type. The link and block definitions use its actual triples and apply to every such H. Under the cap of at most four neighbors per ground pair, a complete four-by-four block saturates every pair joining its center to its support. Its support is then a whole connected component of the center's link.

**Definition 1.1 (Vertex links).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponents.link`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFComponents.link` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The simple graph L(c) has an edge xy precisely when x and y are distinct, both differ from c, and {c,x,y} belongs to H.

**Definition 1.2 (Complete four-by-four configurations).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponents.CompleteBlock`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFComponents.CompleteBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A block consists of two disjoint four-element sets A and S, a center c outside both, and every triple {c,x,y} for x in A and y in S in H. This predicate refers only to actual triples.

**Definition 1.3 (Counting by center and support).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponents.blocks`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFComponents.blocks` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite block set contains pairs (c,U) with an eight-element support U admitting such a bipartition. The two sides and their ordering are existential witnesses, not counted objects.

**Definition 1.4 (The center/support block count).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponents.B`

*Formalization.* `D5/S3/Combinatorics/Graph/DUFComponents.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(H) is the cardinality of the center/support block set for any H. Under the codegree cap of four, the component equivalence identifies it with the total number of connected K4,4 components in all vertex links, counted by center and support.

**Theorem 1.5 (Reciprocal four-star fibers).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponents.reciprocal_four_fiber`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFComponents.reciprocal_four_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and the cap, if S has four vertices and F(S) has four edges, there are a center c and a four-element leaf set A forming a complete block (c,A,S), with F(S)=cA and F(A)=cS. Every representation F(S)=dT with d outside T satisfies d=c and T=A.

**Theorem 1.6 (Saturation gives an entire component).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponents.block_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFComponents.block_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying the cap and a complete block (c,A,S), N({c,x})=S for every x in A and N({c,y})=A for every y in S. For every x in A union S and every ground vertex y, link adjacency holds exactly when x is in A and y is in S, or x is in S and y is in A. Thus there are no outgoing edges. Paths of length at most two connect A union S, which equals the support of an actual connected component of L(c).

**Theorem 1.7 (Exact component semantics).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponents.blocks_iff_component`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFComponents.blocks_iff_component` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying the cap, (c,U) belongs to the block set if and only if U is the support of a connected component of L(c) admitting disjoint four-element parts A and S with U=A union S and the following adjacency: for every x in U and every ground vertex y, xy is an edge exactly when x is in A and y is in S, or x is in S and y is in A. The reverse direction recovers the actual triples and excludes c from U.

**Theorem 1.8 (Both fibers of a complete block).**

Lean statement: `D5/S3/Combinatorics/Graph/DUFComponents.block_fibers`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/DUFComponents.block_fibers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For H satisfying DUF and the cap and every complete block (c,A,S) in H, F(S)=cA and F(A)=cS. The cap saturates neighborhoods, while the intersecting-family bound excludes additional fiber edges.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponents.B`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponents.CompleteBlock`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponents.block_component`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponents.block_fibers`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponents.blocks`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponents.blocks_iff_component`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponents.link`
- Truth anchor: `D5/S3/Combinatorics/Graph/DUFComponents.reciprocal_four_fiber`
- Dependency: [D5/S3/Combinatorics/Graph/DUFCounting](DUFCounting.md)
