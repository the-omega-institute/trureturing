# Sparse Character Synchronization

## Abstract

Sparse comparisons synchronize a common phase exactly on preconnected graphs.

**Definition 1.1 (Sparse comparisons).**

$$\forall (V: Type) (G: \operatorname{SimpleGraph}(V)) (A: Type) [\operatorname{AddCommGroup}(A)] (x: V \to A) (e: \operatorname{E}(G)), \operatorname{edgeDifference}(G, A, x, e) = \operatorname{x}(\operatorname{fst}(e)) - \operatorname{x}(\operatorname{snd}(e))$$

*Formalization.* `D5/S3/Factorization/Galois/SparseCharacterSynchronization.edgeDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let E(G) consist of ordered pairs of adjacent vertices. The additive homomorphism edgeDifference sends a vertex label x to the edge label x(u) minus x(v). All comparisons take place in the same group A.

**Theorem 1.2 (Exact synchronization criterion).**

$$\forall (V: Type) (G: \operatorname{SimpleGraph}(V)) (A: Type) [\operatorname{AddCommGroup}(A)] [\operatorname{Nontrivial}(A)],\\\operatorname{ker}(\operatorname{edgeDifference}(G, A)) = \operatorname{range}(\operatorname{Pi.constAddMonoidHom}(V, A)) \iff \operatorname{Preconnected}(G)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Galois/SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any simple graph G and nontrivial abelian additive group A, the edge-difference kernel equals the diagonal subgroup if and only if G is preconnected: every two vertices are joined by a finite path. Vertex and edge sets need not be finite.

The upstream additive homomorphism Pi.constAddMonoidHom V A sends a value a in A to the vertex labeling w mapped to a. Its range is the diagonal subgroup of constant labels.

A zero difference forces equal labels at both endpoints. Induction along a path propagates that equality. A nonempty vertex set provides the common value; on the empty vertex set the zero phase represents the unique labeling.

Conversely, fix a vertex and a nonzero coefficient. Give the reachable component value zero and its complement the nonzero value. This labeling has zero difference on every edge. If all kernel labels are constant, the complement must be empty.

For cyclic coefficient groups of orders four and three, the criterion synchronizes common character values through any connected comparison graph. It does not identify elements of distinct finite fields. Arithmetic normalization, prime roles and denominator conditions remain separate hypotheses in any arithmetic application.

## References

- Truth anchor: `D5/S3/Factorization/Galois/SparseCharacterSynchronization.edgeDifference`
- Truth anchor: `D5/S3/Factorization/Galois/SparseCharacterSynchronization.edge_difference_kernel_eq_constants_iff`
