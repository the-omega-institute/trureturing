# Contextual rotations and tree bracket coordinates

## Abstract

Contextual right rotations generate the coordinate order on tree brackets.

**Definition 1.1 (Full binary trees).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.FullTree`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.FullTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FullTree is Mathlib’s BinaryTree Unit. An empty node is a leaf.

**Definition 1.2 (Trees at a fixed rank).**

$$\forall m \in \mathbb{N},\; \operatorname{Trees}\left(m\right) = \{t \mid t \in FullTree \land \operatorname{numNodes}\left(t\right) = m\}$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.Trees` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Trees(m) contains exactly the full trees with m internal nodes and hence m + 1 leaves.

**Definition 1.3 (Inorder endpoints).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.treeBrackets`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.treeBrackets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At each internal inorder index, record the rightmost internal index of the subtree rooted there. The resulting function is a bracketing function.

**Definition 1.4 (A right rotation in context).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.RightRotation`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.RightRotation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The root step takes ((X Y) Z) to (X (Y Z)). A step in either child also gives a step on the whole tree with the other child fixed.

**Definition 1.5 (Rotation reachability).**

$$RotationReach = \operatorname{ReflTransGen}\left(RightRotation\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.RotationReach` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

RotationReach is the reflexive transitive closure of RightRotation.

**Theorem 1.6 (Reachability equals bracket order).**

$$\forall m \in \mathbb{N},\; \forall t \in \operatorname{Trees}\left(m\right),\; \forall u \in \operatorname{Trees}\left(m\right),\; \operatorname{RotationReach}\left(\operatorname{val}\left(t\right), \operatorname{val}\left(u\right)\right) \Leftrightarrow (\operatorname{treeBrackets}\left(t\right) \le \operatorname{treeBrackets}\left(u\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.rotationReach_iff_bracket_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rotation increases one endpoint. Conversely, at the first unequal coordinate one can rotate while staying below the target bracket. The sum of remaining endpoint deficits decreases.

**Definition 1.7 (The Tamari partial order).**

$$\forall m \in \mathbb{N},\; \forall t \in \operatorname{Trees}\left(m\right),\; \forall u \in \operatorname{Trees}\left(m\right),\; (t \le u) \Leftrightarrow \operatorname{RotationReach}\left(\operatorname{val}\left(t\right), \operatorname{val}\left(u\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.tamariPartialOrder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order relation on fixed-rank trees is RotationReach on the underlying trees.

**Definition 1.8 (The tree bracket order isomorphism).**

Lean statement: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.treeBracketOrderIso`

*Formalization.* `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.treeBracketOrderIso` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Inorder endpoint arrays determine their tree. Tree reconstruction gives every bracket array, and the rotation criterion identifies the two orders.

## References

- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.FullTree`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.RightRotation`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.RotationReach`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.Trees`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.rotationReach_iff_bracket_le`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.tamariPartialOrder`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.treeBracketOrderIso`
- Truth anchor: `D5/S3/Combinatorics/Lattices/Tamari/TreeRotations.treeBrackets`
- Dependency: [D5/S3/Combinatorics/Lattices/Tamari/BracketRows](BracketRows.md)
