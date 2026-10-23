# Full block determinant quartets on trees

## Abstract

The full determinant quartet for a real tree response with only the eliminated block positive definite.

Every vertex has the same complete real fibre. Blocks are read in the original coordinate basis. Edge blocks may be singular or zero, and diagonal blocks are unrestricted except for the stated positivity of the eliminated principal block.

**Definition 1.1 (A repeated minimum).**

$$\forall x \in \operatorname{Real},\; \forall y \in \operatorname{Real},\; \forall z \in \operatorname{Real},\; \operatorname{RepeatedMin}\left(x, y, z\right) = \left(\left(x = y \land y \le z\right) \lor \left(\left(x = z \land z \le y\right) \lor \left(y = z \land z \le x\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.RepeatedMin` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three possible equalities include the case where all three values coincide.

**Definition 1.2 (Complete vertex blocks).**

$$\forall V \in \operatorname{Type},\; \forall r \in \operatorname{Nat},\; \forall M \in \operatorname{Matrix}\left(V \times \operatorname{Fin}\left(r\right), V \times \operatorname{Fin}\left(r\right), \operatorname{Real}\right),\; \forall x \in V,\; \forall y \in V,\; \forall i \in \operatorname{Fin}\left(r\right),\; \forall j \in \operatorname{Fin}\left(r\right),\; \operatorname{block}\left(M, x, y\right)\left(i, j\right) = M\left((x, i), (y, j)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.block` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The row and column maps keep all r coordinates of each named actual vertex.

**Definition 1.3 (Absolute full determinants).**

$$\forall V \in \operatorname{Type},\; \forall r \in \operatorname{Nat},\; \forall M \in \operatorname{Matrix}\left(V \times \operatorname{Fin}\left(r\right), V \times \operatorname{Fin}\left(r\right), \operatorname{Real}\right),\; \forall x \in V,\; \forall y \in V,\; \operatorname{weight}\left(M, x, y\right) = \lvert \operatorname{det}\left(\operatorname{block}\left(M, x, y\right)\right) \rvert$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the determinant of the entire r by r block, followed by absolute value. It is not an operator norm or a selected singular value.

**Definition 1.4 (Tree support).**

$$\forall V \in \operatorname{Type},\; \forall r \in \operatorname{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall M \in \operatorname{Matrix}\left(V \times \operatorname{Fin}\left(r\right), V \times \operatorname{Fin}\left(r\right), \operatorname{Real}\right),\; \operatorname{Supported}\left(G, M\right) = \left(\forall x \in V,\; \forall y \in V,\; x \ne y \Rightarrow \left(\left(\neg \operatorname{Adj}\left(G, x, y\right)\right) \Rightarrow \operatorname{block}\left(M, x, y\right) = 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.Supported` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Distinct nonadjacent vertices have zero blocks. The condition allows arbitrary diagonal blocks and arbitrary rank on every edge.

**Definition 1.5 (Three pairings).**

$$\forall V \in \operatorname{Type},\; \forall d \in V \to \left(V \to \operatorname{Real}\right),\; \forall a \in V,\; \forall b \in V,\; \forall c \in V,\; \forall e \in V,\; \operatorname{Quartet}\left(d, a, b, c, e\right) = \operatorname{RepeatedMin}\left(d\left(a, b\right) \cdot d\left(c, e\right), d\left(a, c\right) \cdot d\left(b, e\right), d\left(a, e\right) \cdot d\left(b, c\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.Quartet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three products correspond to the perfect matchings ab|ce, ac|be, and ae|bc. This predicate also allows coincident marked vertices.

**Definition 1.6 (Original rectangular restrictions).**

$$\forall V \in \operatorname{Type},\; \forall r \in \operatorname{Nat},\; \forall Q \in \operatorname{Matrix}\left(V \times \operatorname{Fin}\left(r\right), V \times \operatorname{Fin}\left(r\right), \operatorname{Real}\right),\; \forall B \in \operatorname{Set}\left(V\right),\; \forall C \in \operatorname{Set}\left(V\right),\; \forall x \in B \times \operatorname{Fin}\left(r\right),\; \forall y \in C \times \operatorname{Fin}\left(r\right),\; \operatorname{cut}\left(Q, B, C\right)\left(x, y\right) = Q\left((\operatorname{val}\left(\operatorname{fst}\left(x\right)\right), \operatorname{snd}\left(x\right)), (\operatorname{val}\left(\operatorname{fst}\left(y\right)\right), \operatorname{snd}\left(y\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restrictions select coordinates without recalculating any diagonal entry. The type B denotes the subtype of vertices belonging to B.

**Definition 1.7 (Eliminating the complement).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall r \in \operatorname{Nat},\; \forall Q \in \operatorname{Matrix}\left(V \times \operatorname{Fin}\left(r\right), V \times \operatorname{Fin}\left(r\right), \operatorname{Real}\right),\; \forall B \in \operatorname{Set}\left(V\right),\; [\operatorname{DecidableMembership}\left(B\right)] \operatorname{response}\left(Q, B\right) = \operatorname{cut}\left(Q, B, B\right) - \operatorname{cut}\left(Q, B, \operatorname{compl}\left(B\right)\right) \cdot \operatorname{cut}\left(Q, \operatorname{compl}\left(B\right), \operatorname{compl}\left(B\right)\right)^{-1} \cdot \operatorname{cut}\left(Q, \operatorname{compl}\left(B\right), B\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the complement of B is eliminated. In the four selected response blocks, every extra retained vertex is grounded at zero. An empty complement gives a zero elimination term.

**Theorem 1.8 (The inverse-tree quartet).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall r \in \operatorname{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall Q \in \operatorname{Matrix}\left(V \times \operatorname{Fin}\left(r\right), V \times \operatorname{Fin}\left(r\right), \operatorname{Real}\right),\; \operatorname{IsTree}\left(G\right) \Rightarrow \left(\operatorname{IsHermitianPositiveDefinite}\left(Q\right) \Rightarrow \left(\operatorname{Supported}\left(G, Q\right) \Rightarrow \left(\forall a \in V,\; \forall b \in V,\; \forall c \in V,\; \forall e \in V,\; \operatorname{RepeatedMin}\left(\operatorname{weight}\left(Q^{-1}\right)\left(a, b\right) \cdot \operatorname{weight}\left(Q^{-1}\right)\left(c, e\right), \operatorname{weight}\left(Q^{-1}\right)\left(a, c\right) \cdot \operatorname{weight}\left(Q^{-1}\right)\left(b, e\right), \operatorname{weight}\left(Q^{-1}\right)\left(a, e\right) \cdot \operatorname{weight}\left(Q^{-1}\right)\left(b, c\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.inverse_tree_quartet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Delete a leaf v with neighbor u and take its positive-definite diagonal Schur complement. The remaining inverse is the principal inverse block. Every cross block from v factors through u with the actual leaf transport matrix. The leaf diagonal inverse is its positive conditional covariance plus the transported neighbor covariance. The existing Gram determinant comparison bounds the determinant of the transported part, including singular transport. Induction on the number of vertices proves the quartet. When a marked leaf is replaced by its neighbor, marked vertices may coincide; the repeated-vertex induction statement handles this case.

**Theorem 1.9 (The actual-response quartet).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall r \in \operatorname{Nat},\; \forall T \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{Matrix}\left(V \times \operatorname{Fin}\left(r\right), V \times \operatorname{Fin}\left(r\right), \operatorname{Real}\right),\; \operatorname{IsTree}\left(T\right) \Rightarrow \left(\operatorname{IsSymm}\left(H\right) \Rightarrow \left(\operatorname{Supported}\left(T, H\right) \Rightarrow \left(\forall z \in \operatorname{Real},\; \forall B \in \operatorname{Set}\left(V\right),\; [\operatorname{DecidableMembership}\left(B\right)] \operatorname{IsHermitianPositiveDefinite}\left(\operatorname{cut}\left(H - z \cdot 1, \operatorname{compl}\left(B\right), \operatorname{compl}\left(B\right)\right)\right) \Rightarrow \left(\forall P \in \operatorname{Embedding}\left(\operatorname{Fin}\left(4\right), B\right),\; \operatorname{RepeatedMin}\left(\operatorname{weight}\left(\operatorname{response}\left(H - z \cdot 1, B\right)\right)\left(P\left(0\right), P\left(1\right)\right) \cdot \operatorname{weight}\left(\operatorname{response}\left(H - z \cdot 1, B\right)\right)\left(P\left(2\right), P\left(3\right)\right), \operatorname{weight}\left(\operatorname{response}\left(H - z \cdot 1, B\right)\right)\left(P\left(0\right), P\left(2\right)\right) \cdot \operatorname{weight}\left(\operatorname{response}\left(H - z \cdot 1, B\right)\right)\left(P\left(1\right), P\left(3\right)\right), \operatorname{weight}\left(\operatorname{response}\left(H - z \cdot 1, B\right)\right)\left(P\left(0\right), P\left(3\right)\right) \cdot \operatorname{weight}\left(\operatorname{response}\left(H - z \cdot 1, B\right)\right)\left(P\left(1\right), P\left(2\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.complete263_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write Q = H - z Id and S for its Schur response on B. Add a common positive diagonal m Id at all retained vertices. Internal positivity and a spectral bound for S make this auxiliary tree matrix positive definite for every sufficiently large m. Its inverse restricted to B is (S + m Id) inverse. The inverse-tree quartet therefore applies to all four actual ports, regardless of their degrees or positions. The matrix S (Id + S/m) inverse equals m Id - m squared times (S + m Id) inverse and converges to S. Its six off-diagonal blocks are common scalar multiples of the corresponding auxiliary inverse blocks. Full determinants preserve this common scaling, and the repeated-minimum condition is closed under limits. This proves the original response law with no global positivity. The embedding of Fin 4 into B supplies four distinct ordered actual ports and entails at least four vertices. The theorem permits every natural r, so in particular includes all required r at least one; the zero-dimensional extension imposes no restriction on the stated result. Neither the construction nor the limit changes the original basis or units.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.Quartet`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.RepeatedMin`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.Supported`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.block`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.complete263_2`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.cut`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.inverse_tree_quartet`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.response`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeResponseQuartet.weight`
- Dependency: [D5/S3/Arith/AbsoluteValues/Heights/Hadamard](../../Arith/AbsoluteValues/Heights/Hadamard.md)
