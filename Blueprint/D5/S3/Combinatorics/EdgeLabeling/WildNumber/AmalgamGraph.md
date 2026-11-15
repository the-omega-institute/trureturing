# AmalgamGraph

## Abstract

Finite edge-colored graphs and their greedy color-connecting sets.

**Theorem 1.1 (embed injective).**

$$\forall (\iota \operatorname{A} : \operatorname{Type}) (\operatorname{i} : \iota) , \operatorname{Function} . \operatorname{Injective} (\operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{i}) : \operatorname{Option} \operatorname{A} \to \operatorname{Option} (\iota \times \operatorname{A}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.embed_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Definition 1.2 (starGraph).**

$$\forall (\iota \operatorname{A} : \operatorname{Type}) (\operatorname{F} : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) (\operatorname{x} \operatorname{y} : \operatorname{Option} (\iota \times \operatorname{A})) , (\operatorname{starGraph} \operatorname{F}) . \operatorname{Adj} \operatorname{x} \operatorname{y} \iff \exists (\operatorname{i} : \iota) (\operatorname{u} \operatorname{v} : \operatorname{Option} \operatorname{A}) , (\operatorname{F} \operatorname{i}) . \operatorname{Adj} \operatorname{u} \operatorname{v} \land \operatorname{x} = \operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{i}) \operatorname{u} \land \operatorname{y} = \operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{i}) \operatorname{v}$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.starGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Theorem 1.3 (reachable map of adj).**

$$\forall \{ \operatorname{V} : \operatorname{Type} \} \{ \operatorname{W} : \operatorname{Type} \} \{ \operatorname{G} : \operatorname{SimpleGraph} \operatorname{V} \} \{ \operatorname{H} : \operatorname{SimpleGraph} \operatorname{W} \} (\operatorname{f} : \operatorname{V} \to \operatorname{W}) , (\forall \{ \operatorname{u} \operatorname{v} : \operatorname{V} \} , \operatorname{G} . \operatorname{Adj} \operatorname{u} \operatorname{v} \to \operatorname{H} . \operatorname{Reachable} (\operatorname{f} \operatorname{u}) (\operatorname{f} \operatorname{v})) \to \forall \{ \operatorname{u} \operatorname{v} : \operatorname{V} \} , \operatorname{G} . \operatorname{Reachable} \operatorname{u} \operatorname{v} \to \operatorname{H} . \operatorname{Reachable} (\operatorname{f} \operatorname{u}) (\operatorname{f} \operatorname{v})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.reachable_map_of_adj` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Theorem 1.4 (connected star iff).**

$$\forall \{ \iota : \operatorname{Type} \} \{ \operatorname{A} : \operatorname{Type} \} (\operatorname{F} : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) , (\operatorname{AmalgamGraph} . \operatorname{starGraph} \operatorname{F}) . \operatorname{Connected} \iff \forall (\operatorname{i} : \iota) , (\operatorname{F} \operatorname{i}) . \operatorname{Connected}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.connected_star_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Theorem 1.5 (liftEdge injective).**

$$\forall (\iota \operatorname{A} : \operatorname{Type}) (\operatorname{i} : \iota) , \operatorname{Function} . \operatorname{Injective} (\operatorname{Sym2} . \operatorname{map} (\operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{i})) : \operatorname{Sym2} (\operatorname{Option} \operatorname{A}) \to \operatorname{Sym2} (\operatorname{Option} (\iota \times \operatorname{A})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.liftEdge_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Theorem 1.6 (liftEdge block unique).**

$$\forall \{ \iota : \operatorname{Type} \} \{ \operatorname{A} : \operatorname{Type} \} \{ \operatorname{i} \operatorname{j} : \iota \} \{ \operatorname{e} \operatorname{f} : \operatorname{Sym2} (\operatorname{Option} \operatorname{A}) \} , \neg \operatorname{e} . \operatorname{IsDiag} \to \operatorname{Sym2} . \operatorname{map} (\operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{i})) \operatorname{e} = \operatorname{Sym2} . \operatorname{map} (\operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{j})) \operatorname{f} \to \operatorname{i} = \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.liftEdge_block_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Theorem 1.7 (liftEdgeMem).**

$$\forall \{ \iota : \operatorname{Type} \} \{ \operatorname{A} : \operatorname{Type} \} (\operatorname{B} : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) (\operatorname{i} : \iota) \{ \operatorname{e} : \operatorname{Sym2} (\operatorname{Option} \operatorname{A}) \} , \operatorname{e} \in (\operatorname{B} \operatorname{i}) . \operatorname{edgeSet} \to \operatorname{Sym2} . \operatorname{map} (\operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{i})) \operatorname{e} \in (\operatorname{AmalgamGraph} . \operatorname{starGraph} \operatorname{B}) . \operatorname{edgeSet}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.liftEdgeMem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Theorem 1.8 (star edge decomp).**

$$\forall \{ \iota : \operatorname{Type} \} \{ \operatorname{A} : \operatorname{Type} \} (\operatorname{B} : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) \{ \operatorname{e} : \operatorname{Sym2} (\operatorname{Option} (\iota \times \operatorname{A})) \} , \operatorname{e} \in (\operatorname{AmalgamGraph} . \operatorname{starGraph} \operatorname{B}) . \operatorname{edgeSet} \iff \exists \operatorname{i} , \exists \operatorname{f} \in (\operatorname{B} \operatorname{i}) . \operatorname{edgeSet} , \operatorname{Sym2} . \operatorname{map} (\operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{i})) \operatorname{f} = \operatorname{e}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.star_edge_decomp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Definition 1.9 (edgeForward).**

$$\forall (\iota \operatorname{A} : \operatorname{Type}) (\operatorname{B} : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) , (\operatorname{edgeForward} \operatorname{B} : (\Sigma \operatorname{i} : \iota , (\operatorname{B} \operatorname{i}) . \operatorname{edgeSet}) \to (\operatorname{starGraph} \operatorname{B}) . \operatorname{edgeSet}) = (\operatorname{fun} (\operatorname{e} : \Sigma \operatorname{i} : \iota , (\operatorname{B} \operatorname{i}) . \operatorname{edgeSet}) \mapsto \langle \operatorname{Sym2} . \operatorname{map} (\operatorname{Option} . \operatorname{map} (\operatorname{Prod} . \operatorname{mk} \operatorname{e} . 1)) \operatorname{e} . 2 . \operatorname{val} , \operatorname{liftEdgeMem} \operatorname{B} \operatorname{e} . 1 \operatorname{e} . 2 . \operatorname{property} \rangle)$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.edgeForward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Theorem 1.10 (edgeForwardBijective).**

$$\forall \{ \iota : \operatorname{Type} \} \{ \operatorname{A} : \operatorname{Type} \} (\operatorname{B} : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) , \operatorname{Function} . \operatorname{Bijective} (\operatorname{AmalgamGraph} . \operatorname{edgeForward} \operatorname{B})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.edgeForwardBijective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Definition 1.11 (edgeEquiv).**

$$\forall (\iota \operatorname{A} : \operatorname{Type}) (\operatorname{B} : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) , (\operatorname{edgeEquiv} \operatorname{B} : \operatorname{Equiv} (\Sigma \operatorname{i} : \iota , (\operatorname{B} \operatorname{i}) . \operatorname{edgeSet}) (\operatorname{starGraph} \operatorname{B}) . \operatorname{edgeSet}) = \operatorname{Equiv} . \operatorname{ofBijective} (\operatorname{edgeForward} \operatorname{B}) (\operatorname{edgeForwardBijective} \operatorname{B})$$

*Formalization.* `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.edgeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

**Theorem 1.12 (component count star difference).**

$$\forall \{ \iota : \operatorname{Type} \} \{ \operatorname{A} : \operatorname{Type} \} [ \operatorname{Fintype} \iota ] [ \operatorname{Finite} \operatorname{A} ] (\operatorname{F} \operatorname{F} ' : \iota \to \operatorname{SimpleGraph} (\operatorname{Option} \operatorname{A})) (\operatorname{i} : \iota) , (\forall (\operatorname{j} : \iota) , \operatorname{j} \neq \operatorname{i} \to \operatorname{F} \operatorname{j} = \operatorname{F} ' \operatorname{j}) \to \operatorname{Nat} . \operatorname{card} (\operatorname{AmalgamGraph} . \operatorname{starGraph} \operatorname{F}) . \operatorname{ConnectedComponent} - \operatorname{Nat} . \operatorname{card} (\operatorname{AmalgamGraph} . \operatorname{starGraph} \operatorname{F} ') . \operatorname{ConnectedComponent} = \operatorname{Nat} . \operatorname{card} (\operatorname{F} \operatorname{i}) . \operatorname{ConnectedComponent} - \operatorname{Nat} . \operatorname{card} (\operatorname{F} ' \operatorname{i}) . \operatorname{ConnectedComponent}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.component_count_star_difference` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The blocks have a common root represented by none; every other vertex retains its block index. Edges lie in a unique block, and the nonroot connected components decompose by block.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.component_count_star_difference`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.connected_star_iff`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.edgeEquiv`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.edgeForward`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.edgeForwardBijective`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.embed_injective`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.liftEdgeMem`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.liftEdge_block_unique`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.liftEdge_injective`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.reachable_map_of_adj`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.starGraph`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/WildNumber/AmalgamGraph.star_edge_decomp`
