# Independence in Cartesian Cayley squares

## Abstract

Independent sets have a per-row upper bound; a difference-set construction attains that bound in finite abelian Cayley squares.

**Theorem 1.1 (Counting independent vertices by rows).**

$$\forall V \in \mathrm{Type},\; \forall W \in \mathrm{Type},\; [\operatorname{Finite}\left(W\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(W\right),\; \forall I \in \operatorname{Finset}\left(\operatorname{Prod}\left(V, W\right)\right),\; \forall R \in \operatorname{Finset}\left(V\right),\; \left(\operatorname{IsIndepSet}\left(\operatorname{boxProd}\left(G, H\right), I\right) \land \left(\forall p \in \operatorname{Prod}\left(V, W\right),\; \operatorname{Mem}\left(p, I\right) \Rightarrow \operatorname{Mem}\left(\operatorname{fst}\left(p\right), R\right)\right)\right) \Rightarrow \operatorname{card}\left(I\right) \le \operatorname{card}\left(R\right) \cdot \operatorname{indepNum}\left(H\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CayleyIndependence.card_le_layer_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In a Cartesian product G □ H with H finite, the second coordinates in each fixed row form an independent set of H. If every selected first coordinate belongs to the finite set R, summing the row bounds gives |I| ≤ |R| alpha(H). The first factor may be infinite; both factors may be empty or disconnected.

**Theorem 1.2 (The full abelian square equality).**

$$\forall A \in \mathrm{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{AddCommGroup}\left(A\right)] \forall S \in \operatorname{Set}\left(A\right),\; \left(\left(\neg \operatorname{Mem}\left(0, S\right)\right) \land \left(\forall z \in A,\; \operatorname{Mem}\left(z, S\right) \Rightarrow \operatorname{Mem}\left(\operatorname{neg}\left(z\right), S\right)\right)\right) \Rightarrow \operatorname{indepNum}\left(\operatorname{boxProd}\left(\operatorname{addCayley}\left(S\right), \operatorname{addCayley}\left(S\right)\right)\right) = \operatorname{FintypeCard}\left(A\right) \cdot \operatorname{indepNum}\left(\operatorname{addCayley}\left(S\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Products/CayleyIndependence.indepNum_addCayley_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be any finite additive abelian group, and let S avoid zero and be closed under negation. The native Cayley adjacency is exactly y-x in S. For a maximum independent set B, the pairs (x,x+b), with x in A and b in B, form an independent set in the Cartesian square. Injectivity gives |A||B| vertices and attains the row bound. Connectedness is unnecessary; the trivial group, an empty connection set, and self-inverse steps are included.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CayleyIndependence.card_le_layer_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/Products/CayleyIndependence.indepNum_addCayley_square`
