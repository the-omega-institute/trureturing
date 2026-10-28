# Tree endpoint moment certificates

## Abstract

Actual rooted finite tree recurrence states and every-order positive Jacobi rigidity.

The coefficient field is arbitrary where stated. Algebraic pairing needs only a field; positivity and the tree norm statements use a linearly ordered field. All vertices and the selected port belong to the same actual finite graph. No spectral, positivity, cyclicity, contraction or oracle premise is added to that graph.

**Definition 1.1 (The original spectral coordinate).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in K,\; \forall c \in K,\; \operatorname{affinePolynomial}\left(a, c\right) = \operatorname{C}\left(c^{-1}\right) \cdot \left(\operatorname{X} - \operatorname{C}\left(a\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.affinePolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Here X denotes the polynomial indeterminate and scalars denote constant polynomials. The formula is c inverse times (X minus a).

**Definition 1.2 (The fixed chain polynomials).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall a \in K,\; \forall c \in K,\; \forall j \in \operatorname{Nat},\; \operatorname{chainPolynomial}\left(a, c, j\right) = \operatorname{comp}\left(\operatorname{ChebyshevS}\left(K, j\right), \operatorname{affinePolynomial}\left(a, c\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.chainPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Mathlib Chebyshev.S has S minus one equal to zero, S zero equal to one, and S at j plus one equal to X times S at j minus S at j minus one. Thus this is precisely the original Q recurrence composed with (z-a)/c; no polynomial is fitted to the observed graph.

**Definition 1.3 (Evaluation at the actual matrix).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall M \in \operatorname{Matrix}\left(V, V, K\right),\; \forall o \in V,\; \forall p \in \operatorname{Polynomial}\left(K\right),\; \operatorname{polynomialVector}\left(M, o, p\right) = \operatorname{mulVec}\left(\operatorname{aeval}\left(M, p\right), \operatorname{unit}\left(o\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.polynomialVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Polynomial evaluation is in the matrix algebra; the resulting matrix acts on the selected unit coordinate.

**Definition 1.4 (Chain states).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall M \in \operatorname{Matrix}\left(V, V, K\right),\; \forall o \in V,\; \forall a \in K,\; \forall c \in K,\; \forall j \in \operatorname{Nat},\; \operatorname{chainVector}\left(M, o, a, c, j\right) = \operatorname{polynomialVector}\left(M, o, \operatorname{chainPolynomial}\left(a, c, j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.chainVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The index is a natural number, beginning with the actual selected unit vector.

**Definition 1.5 (All positive symmetric Jacobi matrices).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{LinearOrder}\left(K\right)] \forall n \in \operatorname{Nat},\; \forall J \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; \operatorname{PositiveJacobi}\left(J\right) \Leftrightarrow \left(\operatorname{IsSymm}\left(J\right) \land \left(\left(\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \left(\operatorname{val}\left(i\right) + 1 < \operatorname{val}\left(j\right) \lor \operatorname{val}\left(j\right) + 1 < \operatorname{val}\left(i\right)\right) \Rightarrow J\left(i, j\right) = 0\right) \land \left(\forall j \in \operatorname{Nat},\; j + 1 < n \Rightarrow 0 < J\left(j, j + 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.PositiveJacobi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every natural order is allowed. The matrix is symmetric, entries farther than one from the diagonal vanish, and every existing adjacent link is strictly positive. The diagonals are unrestricted. The positive-order hypothesis is supplied only where an endpoint vector is needed.

**Definition 1.6 (Absent coordinates mean zero).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall n \in \operatorname{Nat},\; \forall j \in \operatorname{Nat},\; \forall i \in \operatorname{Fin}\left(n\right),\; \operatorname{unitAt}\left(n, j\right)\left(i\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) = j, 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.unitAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero extension lets the rigidity proof treat short, exact and larger matrix orders in the same recurrence.

**Definition 1.7 (Zero-extended diagonals).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall n \in \operatorname{Nat},\; \forall J \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; \forall j \in \operatorname{Nat},\; \operatorname{diagonalAt}\left(J, j\right) = \operatorname{ite}\left(j < n, J\left(j, j\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.diagonalAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed entry uses its natural-number index only in the branch where that index is in range.

**Definition 1.8 (Zero-extended links).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall n \in \operatorname{Nat},\; \forall J \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; \forall j \in \operatorname{Nat},\; \operatorname{nextLink}\left(J, j\right) = \operatorname{ite}\left(j + 1 < n, J\left(j, j + 1\right), 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.nextLink` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

There is no fictitious terminal link: the value is zero when its second endpoint is absent.

**Definition 1.9 (A locally saturated actual stem).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall o \in V,\; \forall z \in V,\; \forall p \in \operatorname{Walk}\left(G, o, z\right),\; \operatorname{IsStem}\left(p\right) \Leftrightarrow \left(\forall j \in \operatorname{Nat},\; j < \operatorname{length}\left(p\right) \Rightarrow \left(\forall x \in V,\; \operatorname{Adj}\left(G, \operatorname{getVert}\left(p, j\right), x\right) \Leftrightarrow \left(\left(0 < j \land x = \operatorname{getVert}\left(p, j - 1\right)\right) \lor x = \operatorname{getVert}\left(p, j + 1\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.IsStem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every proper stem vertex, all actual neighbors are exactly the preceding vertex when present and the following vertex. This predicate alone does not assert existence; the tree theorem earns a simple path satisfying it.

**Definition 1.10 (The actual terminal boundary).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall o \in V,\; \forall z \in V,\; \forall p \in \operatorname{Walk}\left(G, o, z\right),\; \forall x \in V,\; \operatorname{mem}\left(x, \operatorname{forward}\left(p\right)\right) \Leftrightarrow \left(\operatorname{Adj}\left(G, z, x\right) \land \left(\operatorname{length}\left(p\right) = 0 \lor x \ne \operatorname{penultimate}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.forward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only the incoming edge is removed. A zero-length stem removes no edge, so its forward boundary is the actual root's entire neighbor set.

**Definition 1.11 (Rooted endpoint paths).**

$$\forall V \in \operatorname{Type},\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall o \in V,\; \operatorname{EndpointPath}\left(G, o\right) \Leftrightarrow \left(\exists n \in \operatorname{Nat},\; \exists e \in \operatorname{GraphIso}\left(G, \operatorname{pathGraph}\left(n + 1\right)\right),\; e\left(o\right) = 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.EndpointPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A genuine graph isomorphism to a nonempty finite path sends the actual selected port to zero. This includes a singleton and excludes an interior port on a nontrivial path.

**Definition 1.12 (The same actual graph law).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \forall a \in K,\; \forall c \in K,\; \operatorname{uniformMatrix}\left(G, a, c\right) = a \cdot \operatorname{identity}\left(V\right) + c \cdot \operatorname{adjMatrix}\left(K, G\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.uniformMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The adjacency matrix has unit edges and zero diagonal. The shift a is arbitrary, including zero and negative values.

**Definition 1.13 (Squared recurrence norms).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall M \in \operatorname{Matrix}\left(V, V, K\right),\; \forall o \in V,\; \forall a \in K,\; \forall c \in K,\; \forall j \in \operatorname{Nat},\; \operatorname{chainNorm}\left(M, o, a, c, j\right) = \operatorname{dotProduct}\left(\operatorname{chainVector}\left(M, o, a, c, j\right), \operatorname{chainVector}\left(M, o, a, c, j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.chainNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Over the rationals this dot product is the exact sum of squares defining the squared Euclidean length; no square-root normalization is used.

**Definition 1.14 (Actual boundary indicators).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{DecidableEq}\left(V\right)] \forall s \in \operatorname{Finset}\left(V\right),\; \forall x \in V,\; \operatorname{indicatorVector}\left(s\right)\left(x\right) = \operatorname{ite}\left(\operatorname{mem}\left(x, s\right), 1, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.indicatorVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value is one exactly on the given finite set of actual vertices.

**Theorem 1.15 (Moments determine the needed Gram entries).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall W \in \operatorname{Type},\; [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall M \in \operatorname{Matrix}\left(V, V, K\right),\; \forall J \in \operatorname{Matrix}\left(W, W, K\right),\; \operatorname{IsSymm}\left(M\right) \Rightarrow \left(\operatorname{IsSymm}\left(J\right) \Rightarrow \left(\forall o \in V,\; \forall z \in W,\; \forall a \in K,\; \forall c \in K,\; \forall d \in \operatorname{Nat},\; \forall i \in \operatorname{Nat},\; \forall j \in \operatorname{Nat},\; \left(\forall k \in \operatorname{Nat},\; k \le d \Rightarrow \left(M^{k}\right)\left(o, o\right) = \left(J^{k}\right)\left(z, z\right)\right) \Rightarrow \left(i + j \le d \Rightarrow \operatorname{dotProduct}\left(\operatorname{chainVector}\left(M, o, a, c, i\right), \operatorname{chainVector}\left(M, o, a, c, j\right)\right) = \operatorname{dotProduct}\left(\operatorname{chainVector}\left(J, z, a, c, i\right), \operatorname{chainVector}\left(J, z, a, c, j\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.prefix_chain_pairing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expand matrix polynomial evaluation and use symmetry to identify the pairing of powers i and j with moment i+j. The degrees of the fixed chain polynomials are at most their indices. Equal moments through d therefore transfer every pairing with i+j at most d. This helper is consumed by the endpoint classification's prefix-rigidity step.

**Theorem 1.16 (Moments determine the needed diagonal pairings).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall W \in \operatorname{Type},\; [\operatorname{Fintype}\left(W\right)] [\operatorname{DecidableEq}\left(W\right)] \forall M \in \operatorname{Matrix}\left(V, V, K\right),\; \forall J \in \operatorname{Matrix}\left(W, W, K\right),\; \operatorname{IsSymm}\left(M\right) \Rightarrow \left(\operatorname{IsSymm}\left(J\right) \Rightarrow \left(\forall o \in V,\; \forall z \in W,\; \forall a \in K,\; \forall c \in K,\; \forall d \in \operatorname{Nat},\; \forall j \in \operatorname{Nat},\; \left(\forall k \in \operatorname{Nat},\; k \le d \Rightarrow \left(M^{k}\right)\left(o, o\right) = \left(J^{k}\right)\left(z, z\right)\right) \Rightarrow \left(2 \cdot j + 1 \le d \Rightarrow \operatorname{dotProduct}\left(\operatorname{chainVector}\left(M, o, a, c, j\right), \operatorname{mulVec}\left(M, \operatorname{chainVector}\left(M, o, a, c, j\right)\right)\right) = \operatorname{dotProduct}\left(\operatorname{chainVector}\left(J, z, a, c, j\right), \operatorname{mulVec}\left(J, \operatorname{chainVector}\left(J, z, a, c, j\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.prefix_chain_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the same polynomial pairing to p_j and X p_j. The total degree is at most 2j+1. This helper is consumed by the same prefix-rigidity step.

**Theorem 1.17 (Rigidity without an order bound).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{LinearOrder}\left(K\right)] [\operatorname{IsStrictOrderedRing}\left(K\right)] \forall n \in \operatorname{Nat},\; \forall r \in \operatorname{Nat},\; 0 < n \Rightarrow \left(0 < r \Rightarrow \left(\forall J \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), K\right),\; \operatorname{PositiveJacobi}\left(J\right) \Rightarrow \left(\forall a \in K,\; \forall c \in K,\; 0 < c \Rightarrow \left(\left(\forall j \in \operatorname{Nat},\; j < r \Rightarrow \operatorname{dotProduct}\left(\operatorname{chainVector}\left(J, 0, a, c, j\right), \operatorname{chainVector}\left(J, 0, a, c, j\right)\right) = 1\right) \Rightarrow \left(\left(\forall j \in \operatorname{Nat},\; j < r \Rightarrow \operatorname{dotProduct}\left(\operatorname{chainVector}\left(J, 0, a, c, j\right), \operatorname{mulVec}\left(J, \operatorname{chainVector}\left(J, 0, a, c, j\right)\right)\right) = a\right) \Rightarrow \left(r \le n \land \left(\left(\forall j \in \operatorname{Nat},\; j < r \Rightarrow \operatorname{diagonalAt}\left(J, j\right) = a\right) \land \left(\left(\forall j \in \operatorname{Nat},\; j + 1 < r \Rightarrow \operatorname{nextLink}\left(J, j\right) = c\right) \land \operatorname{dotProduct}\left(\operatorname{chainVector}\left(J, 0, a, c, r\right), \operatorname{chainVector}\left(J, 0, a, c, r\right)\right) = \left(c^{-1} \cdot \operatorname{nextLink}\left(J, r - 1\right)\right)^{2} \cdot \operatorname{ite}\left(r < n, 1, 0\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.positive_jacobi_prefix_rigidity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inductively the required unit state forces the next coordinate to exist. Its positive coefficient divided by positive c has square one, hence equals one. The diagonal pairing fixes the next diagonal. Applying the recurrence once more gives the displayed last-link norm, with zero for an exact terminating order. This proves the order bound, all earlier coefficients, and the short, exact and larger-order alternatives over the reals as well as the rationals. No normalized representation or supplied stem is assumed. The classification consumes this result to exclude all rational competitor orders and to force the positive matrix.

**Theorem 1.18 (Earn the first departure on the actual tree).**

$$\forall K \in \operatorname{Type},\; [\operatorname{Field}\left(K\right)] [\operatorname{LinearOrder}\left(K\right)] [\operatorname{IsStrictOrderedRing}\left(K\right)] \forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)] \operatorname{IsTree}\left(G\right) \Rightarrow \left(\left(\forall x \in V,\; \operatorname{degree}\left(G, x\right) \le 3\right) \Rightarrow \left(\forall o \in V,\; \forall a \in K,\; \forall c \in K,\; 0 < c \Rightarrow \left(\exists z \in V,\; \exists p \in \operatorname{Walk}\left(G, o, z\right),\; \operatorname{IsPath}\left(p\right) \land \left(\operatorname{IsStem}\left(p\right) \land \left(1 \le \operatorname{length}\left(p\right) + 1 \land \left(\operatorname{length}\left(p\right) + 1 \le \operatorname{card}\left(V\right) \land \left(\left(\forall i \in \operatorname{Nat},\; i < \operatorname{length}\left(p\right) + 1 \Rightarrow \left(\forall j \in \operatorname{Nat},\; j < \operatorname{length}\left(p\right) + 1 \Rightarrow \operatorname{dotProduct}\left(\operatorname{chainVector}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, i\right), \operatorname{chainVector}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, j\right)\right) = \operatorname{ite}\left(i = j, 1, 0\right)\right)\right) \land \left(\left(\forall j \in \operatorname{Nat},\; j < \operatorname{length}\left(p\right) + 1 \Rightarrow \operatorname{dotProduct}\left(\operatorname{chainVector}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, j\right), \operatorname{mulVec}\left(\operatorname{uniformMatrix}\left(G, a, c\right), \operatorname{chainVector}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, j\right)\right)\right) = a\right) \land \left(\operatorname{chainNorm}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, \operatorname{length}\left(p\right) + 1\right) = \operatorname{card}\left(\operatorname{forward}\left(p\right)\right) \land \left(\left(\operatorname{card}\left(\operatorname{forward}\left(p\right)\right) = 0 \lor \left(\operatorname{card}\left(\operatorname{forward}\left(p\right)\right) = 2 \lor \operatorname{card}\left(\operatorname{forward}\left(p\right)\right) = 3\right)\right) \land \left(\left(0 < \operatorname{length}\left(p\right) \Rightarrow \operatorname{card}\left(\operatorname{forward}\left(p\right)\right) \ne 3\right) \land \left(\left(\operatorname{card}\left(\operatorname{forward}\left(p\right)\right) = 0 \Rightarrow \left(\exists e \in \operatorname{GraphIso}\left(G, \operatorname{pathGraph}\left(\operatorname{length}\left(p\right) + 1\right)\right),\; e\left(o\right) = 0\right)\right) \land \left(\left(\forall j \in \operatorname{Nat},\; j < \operatorname{length}\left(p\right) + 1 \Rightarrow \operatorname{chainVector}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, j\right) = \operatorname{unit}\left(\operatorname{getVert}\left(p, j\right)\right)\right) \land \operatorname{chainVector}\left(\operatorname{uniformMatrix}\left(G, a, c\right), o, a, c, \operatorname{length}\left(p\right) + 1\right) = \operatorname{indicatorVector}\left(\operatorname{forward}\left(p\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.tree_first_departure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose a maximal simple locally saturated rooted stem among the finitely bounded possible lengths. Acyclicity keeps every forward neighbor off that stem. A single forward neighbor would extend it, so maximality excludes boundary size one. The degree bound leaves only zero, two or three; a positive-length stem has at most two forward neighbors. The actual recurrence states are exactly its distinct coordinate vectors, followed by its actual boundary indicator. Thus all earlier norms are one and the next norm is zero, two or three. If the boundary is empty, connectivity exhausts every actual vertex; the path-to-subgraph isomorphism becomes a genuine rooted isomorphism of the whole graph. The theorem supplies, rather than assumes, every stem, Gram and diagonal premise used by the classification.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.EndpointPath`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.IsStem`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.PositiveJacobi`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.affinePolynomial`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.chainNorm`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.chainPolynomial`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.chainVector`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.diagonalAt`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.forward`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.indicatorVector`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.nextLink`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.polynomialVector`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.positive_jacobi_prefix_rigidity`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.prefix_chain_diagonal`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.prefix_chain_pairing`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.tree_first_departure`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.uniformMatrix`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates.unitAt`
