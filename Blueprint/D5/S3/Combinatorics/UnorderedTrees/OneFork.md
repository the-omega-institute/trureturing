# The one-off-path skeleton

## Abstract

An actual finite rooted tree whose size exceeds its vertex-height by one has exactly one leaf outside a deepest root path. The leaf attaches to a nonterminal vertex of that path.

**Definition 1.1 (The original root path).**

$$\operatorname{spine}\left(T, v\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/OneFork.spine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spine is the finite set of parent iterates of v from step zero through its depth, including v and the root. Parent iteration subtracts depth until the root is reached, so these iterates are pairwise distinct on the specified interval. The spine is closed under the parent map and has cardinality depth(v) plus one.

**Theorem 1.2 (A unique omitted leaf).**

$$\operatorname{card}\left(V\right)=\operatorname{height}\left(T\right)+1 \to \exists v, w: V, (\forall x, \operatorname{depth}\left(T, x\right) \le \operatorname{depth}\left(T, v\right)) \land \neg (w \in \operatorname{spine}\left(T, v\right)) \land (\forall x, \neg (x \in \operatorname{spine}\left(T, v\right)) \iff x=w) \land \neg \operatorname{Internal}\left(T, w\right) \land \operatorname{parent}\left(T, w\right) \in \operatorname{spine}\left(T, v\right) \land \operatorname{parent}\left(T, w\right) \neq v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.one_off_spine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite vertex type and actual rooted parent tree T, assume card(V) = height(T) + 1. There exist vertices v and w such that v has maximal depth; w is outside the spine of v; and a vertex x is outside that spine if and only if x = w. The vertex w is a leaf, its parent is on the spine, and that parent is different from v. A deepest vertex exists on the nonempty finite carrier. The spine has exactly height(T) vertices, leaving a singleton complement. A child of the omitted vertex would give a second omitted vertex; an omitted parent would have to equal the vertex itself, contradicting the depth law. Attachment at v would exceed the maximal depth. This includes attachment at the root and the equal-arm boundary.

**Theorem 1.3 (Skeletons of the qualifying actual trees).**

$$\operatorname{height}\left(T\right)=\operatorname{internalCount}\left(T\right) \to \exists h: \operatorname{Internal}\left(T, \operatorname{root}\left(T\right)\right), \exists v, w: \operatorname{InternalVertices}\left(T\right), (\forall x, \operatorname{depth}\left(\operatorname{prune}\left(T, h\right), x\right) \le \operatorname{depth}\left(\operatorname{prune}\left(T, h\right), v\right)) \land \neg (w \in \operatorname{spine}\left(\operatorname{prune}\left(T, h\right), v\right)) \land (\forall x, \neg (x \in \operatorname{spine}\left(\operatorname{prune}\left(T, h\right), v\right)) \iff x=w) \land \neg \operatorname{Internal}\left(\operatorname{prune}\left(T, h\right), w\right) \land \operatorname{parent}\left(\operatorname{prune}\left(T, h\right), w\right) \in \operatorname{spine}\left(\operatorname{prune}\left(T, h\right), v\right) \land \operatorname{parent}\left(\operatorname{prune}\left(T, h\right), w\right) \neq v$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.qualifying_one_off_spine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite actual rooted tree T satisfying vertex-height equals internal-vertex count, the root is internal. There is a deepest path in the pruned tree whose complement is exactly one leaf, attached to a different path vertex from the deepest endpoint. The theorem quantifies the retained vertices on the original internal-vertex subtype and proves all the preceding maximal-depth, complement, leaf and parent properties there. It follows by the leaf-pruning height law and the actual-vertex one-off-path theorem.

**Theorem 1.4 (The canonical fork).**

$$\operatorname{card}\left(V\right)=\operatorname{height}\left(T\right)+1 \implies \exists b,c, \operatorname{Nonempty}\left(\operatorname{Iso}\left(\operatorname{fork}\left(b, c\right), T\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.exists_fork_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any rooted parent tree T on a finite type V of the displayed size, the spine nonterminals are indexed in increasing depth order. The short tip is the omitted vertex and the long tip is the chosen deepest vertex. The short tip attaches at depth b and the long tip at depth b+c. The vertex bijection preserves the root and every parent edge.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.exists_fork_iso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.one_off_spine`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.qualifying_one_off_spine`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.spine`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/LeafPruning](LeafPruning.md)
