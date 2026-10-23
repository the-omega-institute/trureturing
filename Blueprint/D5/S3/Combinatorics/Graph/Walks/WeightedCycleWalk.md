# Actual Even-Cycle Traversals

## Abstract

Actual Even-Cycle Traversals

The graph evenCycleGraph(n) is identified with the usual cycleGraph(2(n+2)) by L(i)->2i+1 and R(i)->2i. The inverse uses parity and integer division. Both directions of adjacency, including the wrap edge, follow from the actual finite cyclic arithmetic. Its circuit begins at L(0) and traverses L(i), R(i+1), L(i+1) in cyclic order. These are actual graph walks, not supplied lists of independent edge weights.

**Theorem 1.1 (Length of the actual circuit).**

$$\forall n \in \mathrm{Nat},\; \mathrm{length}\left(\mathrm{circuit}\left(n\right)\right) = 2 \cdot \left(n + 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The recursively constructed walk adds exactly two edges for each of n+2 indices; endpoint reduction closes it at L(0). Its length is 2(n+2).

**Theorem 1.2 (The traversal is a simple cycle).**

$$\forall n \in \mathrm{Nat},\; \mathrm{IsCycle}\left(\mathrm{circuit}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_isCycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After deleting its initial vertex, the support contains R(i+1),L(i+1) once for each cyclic index. Successor is a permutation, so this list has no repeated vertices. The length is at least four; the path-tail criterion proves IsCycle.

**Theorem 1.3 (Alternating product and actual matchings).**

$$\forall A \in Type,\; [\mathrm{CommGroup}\left(A\right)] \forall n \in \mathrm{Nat},\; \forall w \in \mathrm{Sym2}\left(\mathrm{Sum}\left(\mathrm{Fin}\left(n + 2\right), \mathrm{Fin}\left(n + 2\right)\right)\right) \to A,\; \mathrm{alpha}\left(w, \mathrm{circuit}\left(n\right)\right) = \frac{\prod_{i \in \mathrm{Fin}\left(n + 2\right)} \mathrm{w}\left(\mathrm{s}\left(\operatorname{Sum}.\operatorname{inl}\left(i\right), \operatorname{Sum}.\operatorname{inr}\left(\mathrm{finRotate}\left(n + 2, i\right)\right)\right)\right)}{\prod_{i \in \mathrm{Fin}\left(n + 2\right)} \mathrm{w}\left(\mathrm{s}\left(\operatorname{Sum}.\operatorname{inl}\left(i\right), \operatorname{Sum}.\operatorname{inr}\left(i\right)\right)\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_alpha` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any commutative group and any symmetric edge-weight function w, the existing public WeightedVertexProducts.alpha on this actual circuit equals the product over the actual successor matching divided by the product over the actual paired matching. The proof unfolds the public alpha definition, applies the pinned list alternating-product append identity inside the induction, and reindexes the second edge family by the successor permutation. It does not assume a product bridge.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_alpha`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_isCycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/WeightedCycleWalk.circuit_length`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/WeightedPathCycleRank](WeightedPathCycleRank.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/WeightedVertexProducts](WeightedVertexProducts.md)
