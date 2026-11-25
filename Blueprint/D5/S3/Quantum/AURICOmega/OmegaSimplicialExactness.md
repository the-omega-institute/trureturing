# Finite-chain integration and simplicial cone exactness

## Abstract

Finite-chain integration and simplicial coboundaries in Chapter 32, §32.7.3.2, and the vertex-cone identities in §32.7.5.4. The vertex domain V is an arbitrary sort and Cj consists of A-valued functions on all ordered tuples of j + 1 vertices, with repetitions allowed. The operators d0, d1 and d2 take the alternating sum of omitted-vertex faces. The cone operators H1, H2 and H3 prepend a chosen vertex. Sums, differences and zero are those of the coefficient operations G under their additive abelian group laws.

**Theorem 1.1 (An exact edge difference integrates to the endpoint difference).**

$$\forall V \in Sort, A \in Type, G \in \operatorname{AddCommGroup}\left(A\right), f \in \operatorname{C0}\left(V, A\right), x \in V, y \in V, p \in \operatorname{VertexChain}\left(V, x, y\right),\; \operatorname{Laws}\left(G\right) \Rightarrow \operatorname{sum}\left(p, \operatorname{d0}\left(f\right)\right) = \operatorname{f}\left(y\right) - \operatorname{f}\left(x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.sum_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A chain p from x to y is a finite sequence of oriented edges, possibly empty when the endpoints agree. Each intermediate vertex contributes its potential once with each sign.

**Theorem 1.2 (An exact edge difference has zero sum around a loop).**

$$\forall V \in Sort, A \in Type, G \in \operatorname{AddCommGroup}\left(A\right), f \in \operatorname{C0}\left(V, A\right), b \in V, p \in \operatorname{VertexChain}\left(V, b, b\right),\; \operatorname{Laws}\left(G\right) \Rightarrow \operatorname{sum}\left(p, \operatorname{d0}\left(f\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.sum_d0_loop` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the chain begins and ends at b, its two endpoint values cancel.

**Theorem 1.3 (Two coboundaries of a vertex potential vanish).**

$$\forall V \in Sort, A \in Type, G \in \operatorname{AddCommGroup}\left(A\right), f \in \operatorname{C0}\left(V, A\right), x \in V, y \in V, z \in V,\; \operatorname{Laws}\left(G\right) \Rightarrow \operatorname{d1}\left(\operatorname{d0}\left(f\right), x, y, z\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d1_d0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the alternating sum of the three edge differences, each vertex potential occurs with opposing signs.

**Theorem 1.4 (Two coboundaries of an edge cochain vanish).**

$$\forall V \in Sort, A \in Type, G \in \operatorname{AddCommGroup}\left(A\right), e \in \operatorname{C1}\left(V, A\right), x \in V, y \in V, z \in V, w \in V,\; \operatorname{Laws}\left(G\right) \Rightarrow \operatorname{d2}\left(\operatorname{d1}\left(e\right), x, y, z, w\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d2_d1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each edge appears with opposing signs in the four triangle faces of the ordered quadruple.

**Theorem 1.5 (The cone identity on edges).**

$$\forall V \in Sort, A \in Type, G \in \operatorname{AddCommGroup}\left(A\right), b \in V, e \in \operatorname{C1}\left(V, A\right), x \in V, y \in V,\; \operatorname{Laws}\left(G\right) \Rightarrow \operatorname{d0}\left(\operatorname{H1}\left(b, e\right), x, y\right) + \operatorname{H2}\left(b, \operatorname{d1}\left(e\right), x, y\right) = \operatorname{e}\left(x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d0_H1_add_H2_d1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Prepending b gives two terms on the cone edges. The two terms cancel against the coboundary of the vertex cochain given by H1.

**Theorem 1.6 (The cone identity on triangles).**

$$\forall V \in Sort, A \in Type, G \in \operatorname{AddCommGroup}\left(A\right), b \in V, F \in \operatorname{C2}\left(V, A\right), x \in V, y \in V, z \in V,\; \operatorname{Laws}\left(G\right) \Rightarrow \operatorname{d1}\left(\operatorname{H2}\left(b, F\right), x, y, z\right) + \operatorname{H3}\left(b, \operatorname{d2}\left(F\right), x, y, z\right) = \operatorname{F}\left(x, y, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d1_H2_add_H3_d2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three faces containing the cone vertex cancel when the two summands are added. The face on x, y and z remains.

**Theorem 1.7 (A closed triangle cochain has the chosen cone primitive).**

$$\forall V \in Sort, A \in Type, G \in \operatorname{AddCommGroup}\left(A\right), b \in V, F \in \operatorname{C2}\left(V, A\right),\; \operatorname{Laws}\left(G\right) \Rightarrow \left(\left(\forall x \in V, y \in V, z \in V, w \in V,\; \operatorname{d2}\left(F, x, y, z, w\right) = 0\right) \Rightarrow \left(\forall x \in V, y \in V, z \in V,\; \operatorname{d1}\left(\operatorname{H2}\left(b, F\right), x, y, z\right) = \operatorname{F}\left(x, y, z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d1_H2_of_d2_eq_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a fixed vertex b, the primitive on the edge from x to y is F(b, x, y). Closedness removes the H3 term from the degree-two cone identity.

**Theorem 1.8 (A triangle cochain is closed exactly when it is an edge coboundary).**

$$\forall V \in Sort, A \in Type, G \in \operatorname{AddCommGroup}\left(A\right), b \in V, F \in \operatorname{C2}\left(V, A\right),\; \operatorname{Laws}\left(G\right) \Rightarrow \left(\left(\forall x \in V, y \in V, z \in V, w \in V,\; \operatorname{d2}\left(F, x, y, z, w\right) = 0\right) \Leftrightarrow \left(\exists e \in \operatorname{C1}\left(V, A\right),\; \forall x \in V, y \in V, z \in V,\; \operatorname{d1}\left(e, x, y, z\right) = \operatorname{F}\left(x, y, z\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d2_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward implication uses the primitive H2 at the chosen vertex b. The reverse implication uses vanishing of two successive coboundaries of an edge cochain.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d0_H1_add_H2_d1`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d1_H2_add_H3_d2`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d1_H2_of_d2_eq_zero`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d1_d0`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d2_d1`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.d2_eq_zero_iff`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.sum_d0`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaSimplicialExactness.sum_d0_loop`
