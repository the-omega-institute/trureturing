# Ordered Trees and Original-Leaf Pruning

## Abstract

Finite ordered rooted-tree shapes, exact size fibers, and simultaneous original-leaf pruning.

**Definition 1.1 (Ordered rooted trees).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Tree`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Tree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

A tree consists of one root and a finite ordered list of child trees. There is no empty tree; a root with an empty child list is the singleton. Equality preserves every child position.

**Definition 1.2 (Ordered forests).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Forest`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Forest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

A forest is either empty or a first tree followed by the remaining forest. Its constructors retain sibling order.

**Definition 1.3 (Tree vertex count).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.vertices`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.vertices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

The number of vertices is one plus the total vertex count of the child forest.

**Definition 1.4 (Forest vertex count).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_vertices`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_vertices` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

The total vertex count is the sum of the vertex counts of its trees.

**Definition 1.5 (Vertex height).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

The vertex height is one plus the maximum child height, with empty maximum zero. Thus the singleton has height one.

**Definition 1.6 (Forest height).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_height`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_height` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

The height of a forest is the maximum vertex height of its trees, or zero for the empty forest.

**Definition 1.7 (Nonleaf vertices).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.internal`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.internal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

A root with no children contributes zero; a root with children contributes one plus their nonleaf counts.

**Definition 1.8 (Forest nonleaf count).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_internal`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_internal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

The nonleaf counts of the trees in the ordered forest are added.

**Definition 1.9 (Root-retaining leaf removal).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.prune`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.prune` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

The root is retained and the original leaf children at every level are deleted simultaneously. On every nonsingleton this is exactly original-leaf removal; the singleton is treated separately.

**Definition 1.10 (Order-preserving forest pruning).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.prune_forest`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.prune_forest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Original singleton trees are deleted, and every other tree is pruned in place without permuting its siblings.

**Definition 1.11 (Child and sibling encoding).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.encode`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.encode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

An ordered forest is encoded by its first tree's child forest and its remaining sibling forest. This encoding is used only to enumerate finite size fibers; tree height and nonleaf statistics are always computed on the ordered trees.

**Definition 1.12 (Child and sibling decoding).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decode`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decode` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

A code is decoded to the ordered first tree and remaining siblings. The two encoding maps are inverse, and the code node count equals the forest vertex count.

**Definition 1.13 (Exact size fiber).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.trees`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.trees` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For a positive size, decode every code with one fewer nodes and adjoin its root. Size zero has no tree. The membership theorem proves that this lists every actual ordered shape of that size exactly once.

**Definition 1.14 (Actual height and nonleaf count).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Filter the exact size fiber by equality of vertex height and nonleaf count, then take its cardinality. Each element contributes one to the actual tree count.

**Theorem 1.15 (Finite actual counting interpretation).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For every natural n, the set of ordered shapes with n vertices and height equal to nonleaf count is finite, and its set cardinality equals count n.

**Theorem 1.16 (Exact skeleton predicate).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height_eq_internal_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height_eq_internal_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For every ordered tree, vertex height equals nonleaf count if and only if the tree is not the singleton and its pruned tree has exactly one more vertex than its vertex height.

**Definition 1.17 (Unary ancestors).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.stem`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.stem` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Add b successive unary ancestors without changing child order.

**Definition 1.18 (Path arm).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.path`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.path` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

A path has n unary vertices and one terminal vertex.

**Definition 1.19 (Ordered stem and fork).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.fork`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.fork` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

The stem ends in one binary fork with left and right path arms. Their lengths are retained separately, including the equal-arm case.

**Theorem 1.20 (Exhaustive excess-one classification).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.excess_one_iff_fork`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.excess_one_iff_fork` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For every finite ordered tree, its vertex count exceeds its vertex height by one exactly when it is a unary stem above a binary fork with two path arms, at least one having no unary vertex.

**Theorem 1.21 (Classification of actual pruned shapes).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height_eq_internal_iff_fork`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height_eq_internal_iff_fork` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

An actual tree has height equal to nonleaf count exactly when it is not the singleton and its pruning has this stem and fork form.

**Definition 1.22 (Distinct ordered skeletons).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeletons`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeletons` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For u unary vertices, list every stem with a left path and singleton right arm, then every stem with a singleton left arm and a positive right path. The equal-arm shape occurs only in the first family.

**Theorem 1.23 (Exact all-size skeleton enumeration).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeletons_spec`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeletons_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For every natural u, membership is exactly having u+3 vertices and vertex height u+2, and the finite collection has cardinality 2u+1. Injectivity recovers the stem and both ordered arm lengths, and the two listed orientation families are disjoint.

**Definition 1.24 (Original leaf-gap data).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Decoration`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Decoration` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

A terminal skeleton vertex stores a nonnegative count in addition to one mandatory original leaf. A nonterminal vertex stores the initial leaf gap, its first retained child and the remaining child gaps.

**Definition 1.25 (Remaining child gaps).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.DecorationForest`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.DecorationForest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

A final gap ends the child list; otherwise a gap precedes the next retained child. This stores the ordered gaps without a sibling symmetry quotient.

**Definition 1.26 (Tree inflation).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Replace gap counts by runs of original leaf children. At each terminal vertex insert one mandatory original leaf, so every skeleton vertex remains an internal original vertex.

**Definition 1.27 (Ordered child inflation).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate_forest`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate_forest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Insert each indicated leaf run before its retained child, and insert the final run after the last retained child.

**Definition 1.28 (Undecorated tree).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeleton`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeleton` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Forget all leaf-gap counts while preserving the root and every retained child position.

**Definition 1.29 (Undecorated child forest).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeleton_forest`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeleton_forest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Forget gaps while retaining each child and its order.

**Definition 1.30 (Reversible actual-tree decoration).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decorationEquiv`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decorationEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Ordered gap data are equivalent to actual nonsingleton ordered trees. Extraction reads the maximal original-leaf runs and inflation reconstructs the actual tree; terminal positivity is enforced by the mandatory leaf.

**Theorem 1.31 (Exact pruning of every expansion).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate_prune`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate_prune` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For every decoration, simultaneous original-leaf removal returns exactly its undecorated skeleton. Together with the equivalence, this identifies the entire actual-tree pruning fiber, without a finite cutoff.

**Definition 1.32 (Free leaf total).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.gapTotal`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.gapTotal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Sum all nonnegative gap counts, excluding the one mandatory leaf at each terminal skeleton vertex.

**Definition 1.33 (Free leaves in child gaps).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.gap_total_forest`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.gap_total_forest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Add the current gap count and the free leaf totals of the retained child and remaining child gaps.

**Definition 1.34 (Independent leaf-gap slots).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.slots`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.slots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Count one free gap at a terminal vertex; at a branch count the initial gap, the first retained child's slots and every remaining child gap.

**Definition 1.35 (Slots after retained children).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_slots`

*Formalization.* `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_slots` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

The final child gap contributes one slot; each further retained child contributes its own slots and its preceding gap.

**Theorem 1.36 (Exact size and slot coordinates).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.actual_count_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.actual_count_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

Every actual tree satisfying height equal to nonleaf count has reversible ordered gap data and stem and arm lengths b,l,r with one arm zero. Writing u=b+l+r, the actual vertex count is u+5 plus the free gap total, and the number of free slots is 2u+5.

**Theorem 1.37 (No shapes below size five).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count_eq_zero_of_lt_five`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count_eq_zero_of_lt_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For every natural n less than five, the actual tree count is zero, as a consequence of the exact reconstruction size law. This includes the zero coefficient and the first four required initial values.

**Theorem 1.38 (Weight of a skeleton decoration).**

Lean statement: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decoration_weight`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decoration_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Gus Wiseman; Chai Wah Wu (2024). *OEIS A358588, Ordered rooted trees with height equal to the number of internal nodes*. URL: <https://oeis.org/A358588/internal>.

*Commentary.*

For every decoration whose skeleton belongs to the size-u collection, meaning it has u+3 vertices and vertex height u+2, inflation gives u+5 plus the free gap total vertices, and the decoration has 2u+5 free slots.

## References

- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Decoration`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.DecorationForest`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Forest`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.Tree`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.actual_count_coordinates`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count_eq_zero_of_lt_five`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.count_spec`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decode`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decorationEquiv`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.decoration_weight`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.encode`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.excess_one_iff_fork`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_height`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_internal`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_slots`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.forest_vertices`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.fork`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.gapTotal`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.gap_total_forest`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height_eq_internal_iff`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.height_eq_internal_iff_fork`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate_forest`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.inflate_prune`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.internal`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.path`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.prune`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.prune_forest`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeleton`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeleton_forest`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeletons`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.skeletons_spec`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.slots`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.stem`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.trees`
- Truth anchor: `D5/S3/Combinatorics/OrderedTrees/LeafPruning.vertices`
