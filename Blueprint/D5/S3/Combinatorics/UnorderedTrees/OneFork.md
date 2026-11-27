# The one-off-path skeleton

## Abstract

An actual finite rooted tree whose size exceeds its vertex-height by one has exactly one leaf outside a deepest root path. The leaf attaches to a nonterminal vertex of that path.

**Definition 1.1 (The original root path).**

$$\forall \left(V: Type\right) \left(T: \operatorname{Tree}\left(V\right)\right) \left(v: V\right) , \left(\operatorname{spine}\left(T, v\right) = \left\{\operatorname{iterate}\left(\operatorname{parent}\left(T\right), k, v\right) \mid k \in \operatorname{range}\left(\operatorname{depth}\left(T, v\right)+1\right)\right\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/OneFork.spine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spine is the finite set of parent iterates from v through the root, including both endpoints. It is closed under the parent map and has one vertex for each depth level.

**Theorem 1.2 (A unique omitted leaf).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\left(\operatorname{card}\left(V\right) = \operatorname{height}\left(T\right) + 1\right) \Rightarrow \left(\exists v \in V,\; \exists w \in V,\; \left(\forall x \in V,\; \operatorname{depth}\left(T, x\right) \le \operatorname{depth}\left(T, v\right)\right) \land \left(\left(\neg w \in \operatorname{spine}\left(T, v\right)\right) \land \left(\left(\forall x \in V,\; \left(\neg x \in \operatorname{spine}\left(T, v\right)\right) \Leftrightarrow \left(x = w\right)\right) \land \left(\left(\neg \operatorname{Internal}\left(T, w\right)\right) \land \left(\left(\operatorname{parent}\left(T, w\right) \in \operatorname{spine}\left(T, v\right)\right) \land \left(\operatorname{parent}\left(T, w\right) \ne v\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.one_off_spine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the carrier has one more vertex than the height, a deepest spine leaves a singleton complement. The omitted vertex is a leaf, its parent lies on the spine, and attachment at the deepest endpoint is excluded by maximality.

**Definition 1.3 (The canonical fork carrier).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\operatorname{Fork}\left(b, c\right) = \operatorname{Sum}\left(\operatorname{Fin}\left(b+c+1\right), Bool\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/OneFork.Fork` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fork b c is the sum of the b+c+1 indexed spine vertices and two Boolean-tagged tips.

**Definition 1.4 (The fork point).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\operatorname{forkPoint}\left(b, c\right).val = b\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/OneFork.forkPoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fork point is the spine vertex at index b where the short tip attaches.

**Definition 1.5 (The canonical fork parent map).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\begin{aligned}&\operatorname{root}\left(\operatorname{fork}\left(b, c\right)\right) = \operatorname{inl}\left(0\right)\\&\forall i \in \operatorname{Fin}\left(b+c+1\right),\; \operatorname{parent}\left(\operatorname{fork}\left(b, c\right), \operatorname{inl}\left(i\right)\right) = \operatorname{inl}\left(\langle i.val-1\rangle\right)\\&\operatorname{parent}\left(\operatorname{fork}\left(b, c\right), \operatorname{inr}\left(false\right)\right) = \operatorname{inl}\left(\operatorname{forkPoint}\left(b, c\right)\right)\\&\operatorname{parent}\left(\operatorname{fork}\left(b, c\right), \operatorname{inr}\left(true\right)\right) = \operatorname{inl}\left(\langle b+c\rangle\right)\end{aligned}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical parent map sends each indexed spine vertex to its predecessor and sends the false and true tips to the fork point and terminal spine vertex.

**Theorem 1.6 (Cardinality of the fork).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\operatorname{card}\left(\operatorname{Fork}\left(b, c\right)\right) = b + c + 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.card_fork` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sum carrier has b+c+1 spine vertices and two tips.

**Theorem 1.7 (Height of the fork).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\operatorname{height}\left(\operatorname{fork}\left(b, c\right)\right) = b + c + 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.height_fork` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The long tip attains the maximum depth b+c+1, so the vertex-height is b+c+2.

**Theorem 1.8 (The canonical fork).**

$$\forall \left(V: Type\right) [\operatorname{Fintype}\left(V\right)] \left(T: \operatorname{Tree}\left(V\right)\right) , \left(\left(\operatorname{card}\left(V\right) = \operatorname{height}\left(T\right) + 1\right) \Rightarrow \left(\exists b \in \mathbb{N},\; \exists c \in \mathbb{N},\; \operatorname{Nonempty}\left(\operatorname{Iso}\left(\operatorname{fork}\left(b, c\right), T\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.exists_fork_iso` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A deepest spine, its omitted leaf and the parent edges give a bidirectional labelling by the canonical fork.

**Theorem 1.9 (Internal indexed spine vertices).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\forall i \in \operatorname{Fin}\left(b+c+1\right),\; \operatorname{Internal}\left(\operatorname{fork}\left(b, c\right), \operatorname{inl}\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_internal_spine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every indexed spine vertex has a child, with the terminal position supplied by the long tip.

**Theorem 1.10 (The fork tips are terminal).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\forall p \in Bool,\; \neg \operatorname{Internal}\left(\operatorname{fork}\left(b, c\right), \operatorname{inr}\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Boolean tips have no nonroot children in the canonical parent map.

**Theorem 1.11 (Fork parameters are invariant).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) \left(b': \mathbb{N}\right) \left(c': \mathbb{N}\right) , \left(\forall e: \operatorname{Iso}\left(\operatorname{fork}\left(b, c\right), \operatorname{fork}\left(b', c'\right)\right), \left(\left(b = b'\right) \land \left(c = c'\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_iso_parameters` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An isomorphism between canonical forks identifies the unique branching depth b and then the maximum-depth excess c.

**Theorem 1.12 (Fork isomorphisms fix the spine).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\forall e: \operatorname{Iso}\left(\operatorname{fork}\left(b, c\right), \operatorname{fork}\left(b, c\right)\right), \left(\forall i \in \operatorname{Fin}\left(b+c+1\right),\; e.equiv\left(\operatorname{inl}\left(i\right)\right) = \operatorname{inl}\left(i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_iso_spine` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Depth and internality uniquely identify each indexed nonterminal.

**Theorem 1.13 (Fork isomorphisms permute the tips).**

$$\forall \left(b: \mathbb{N}\right) \left(c: \mathbb{N}\right) , \left(\forall e: \operatorname{Iso}\left(\operatorname{fork}\left(b, c\right), \operatorname{fork}\left(b, c\right)\right), \left(\left(\left(e.equiv\left(\operatorname{inr}\left(false\right)\right) = \operatorname{inr}\left(false\right)\right) \land \left(e.equiv\left(\operatorname{inr}\left(true\right)\right) = \operatorname{inr}\left(true\right)\right)\right) \lor \left(\left(c = 0\right) \land \left(\left(e.equiv\left(\operatorname{inr}\left(false\right)\right) = \operatorname{inr}\left(true\right)\right) \land \left(e.equiv\left(\operatorname{inr}\left(true\right)\right) = \operatorname{inr}\left(false\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_iso_tips` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two tips are the only terminal vertices outside the spine. Their depths distinguish them when c is positive, while c=0 permits the swap.

**Definition 1.14 (The equal-arm tip swap).**

$$\forall \left(b: \mathbb{N}\right) , \left(\operatorname{swapTips}\left(b\right): \operatorname{Iso}\left(\operatorname{fork}\left(b, 0\right), \operatorname{fork}\left(b, 0\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/OneFork.swapTips` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When c=0, exchanging the two Boolean tips is a rooted parent-map isomorphism.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.Fork`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.card_fork`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.exists_fork_iso`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.forkPoint`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_internal_spine`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_iso_parameters`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_iso_spine`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_iso_tips`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.fork_terminal`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.height_fork`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.one_off_spine`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.spine`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/OneFork.swapTips`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/LeafPruning](LeafPruning.md)
