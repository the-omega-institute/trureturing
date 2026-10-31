# Binary hair-tree grafts vanish in the actual Jacobi quotient

## Abstract

Binary hair-tree grafts vanish in the actual Jacobi quotient

**Definition 1.1 (Geometric placement with a trivalent parent).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.HairPlacement`

*Formalization.* `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.HairPlacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A HairPlacement G t is an injective embedding of the actual finite tree flags into G. It preserves the rotor, ordinary colors and every internal mate; the open root is paired to a disjoint actual trivalent parent. Restricting to a left or right subtree rotates its parent to the appropriate actual binary vertex, preserving the whole exterior graph.

**Theorem 1.2 (A placed branching tree contains an actual cherry).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.extractCherry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.extractCherry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite ordinary red and blue binary tree t with at least two leaves, every actual HairPlacement G t yields Nonempty (Cherry G). A one-hole shape context is followed through the injective flag embedding to a terminal pair of leaves. The extracted six flags consist of the terminal binary vertex and its actual parent. Their mate and rotor equations give the literal X socket, with no change to the exterior pairing. This is the structural bridge consumed by the vanishing theorem.

**Theorem 1.3 (Vanishing for every actual graft with at least two leaves).**

Lean statement: `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.branching_hair_tree_vanishes`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.branching_hair_tree_vanishes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite flag type F, every actual cyclic flag graph G on F with arbitrary numbered exterior anchors, every a in F and every ordinary red and blue binary tree t with at least two leaves, classOf (G.graft a t.model) is zero in the actual rational AS, IHX and ordinary CL quotient. The explicit subdividing graft provides a HairPlacement; structural context descent extracts an actual cherry, and the local AS, IHX and CL proof kills the entire graph. This proves the explicitly grafted binary-tree case within the ordinary branching-tree discussion of Proposition 2.2 and Equation 2.2 in MARKED_TWO_COLOR_FOUR_LOOP_JACOBI_VANISHING. A representation theorem from an arbitrary acyclic graph component to HairTree or HairPlacement remains unproved here, as do the global core presentation and four-loop vanishing. The colors remain ordinary throughout, including singleton colors; they are not numbered anchors.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.HairPlacement`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.branching_hair_tree_vanishes`
- Truth anchor: `D5/S3/Combinatorics/Graph/Jacobi/HairPlacement.extractCherry`
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/BranchingHairTree](BranchingHairTree.md)
- Dependency: [D5/S3/Combinatorics/Graph/Jacobi/CherryReduction](CherryReduction.md)
