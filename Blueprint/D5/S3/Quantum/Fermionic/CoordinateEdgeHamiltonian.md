# Real quadratic edge interactions

## Abstract

Real conference coefficients realize normalized quadratic coordinate interactions.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Definition 1.1 (Real quadratic inter-site term).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall w \in \mathrm{Fin}\left(n\right),\; \forall K \in \mathrm{Matrix}\left(\operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \mathrm{quadraticEdge}\left(v, w, K\right) = \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\operatorname{SMul}.\operatorname{smul}\left(\operatorname{Complex}.\operatorname{I}, \sum_{p:\operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)}(\sum_{t:\operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)}(\operatorname{SMul}.\operatorname{smul}\left((\mathrm{val}\left(K, p, t\right):\mathit{Complex}), \operatorname{majorana}\left(n \cdot m, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(v, \operatorname{Prod}.\operatorname{fst}\left(p\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right) \cdot \operatorname{majorana}\left(n \cdot m, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(w, \operatorname{Prod}.\operatorname{fst}\left(t\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(t\right)\right)\right)))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.quadraticEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real coefficient matrix multiplies the actual Jordan-Wigner Majorana matrices, with the factor i exactly as displayed.

**Definition 1.2 (Literal edge average).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \forall K \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \mathrm{averagedHamiltonian}\left(G, K\right) = \operatorname{SMul}.\operatorname{smul}\left(\operatorname{Inv}.\operatorname{inv}\left((\operatorname{Finset}.\operatorname{card}\left(\operatorname{SimpleGraph}.\operatorname{edgeFinset}\left(G\right)\right):\mathit{Real})\right), \sum_{z:\operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right)}(\mathrm{quadraticEdge}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right), \mathrm{val}\left(K, z\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.averagedHamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum runs over all actual unordered edges and is multiplied by the reciprocal of their cardinality.

**Definition 1.3 (Interaction admissibility).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \forall K \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; (\mathrm{admissibleEdges}\left(G, K\right)) \Leftrightarrow (\forall z \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(G\right),\; ((\mathrm{IsSelfAdjoint}\left(\mathrm{quadraticEdge}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right), \mathrm{val}\left(K, z\right)\right)\right)) \land (\left\lVert \mathrm{quadraticEdge}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right), \mathrm{val}\left(K, z\right)\right) \right\rVert \le 1)) \land (\mathrm{Commute}\left(\mathrm{quadraticEdge}\left(\operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right), \mathrm{val}\left(K, z\right)\right), \operatorname{CStarMatrix}.\operatorname{ofMatrix}\left(\mathrm{numberParity}\left(n \cdot m\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.admissibleEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Admissibility means Hermitian, operator norm at most one, and commutation with total occupation parity on each edge.

**Definition 1.4 (Conference edge coefficients).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right)\right),\; \forall a \in \mathrm{Equiv}\left(\mathrm{Fin}\left(q\right), \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)\right),\; \forall z \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{SimpleGraph}.\operatorname{comap}\left(\operatorname{coordinateGraph}\left(q, \operatorname{Index}\left(r\right)\right), e\right)\right),\; \forall p \in \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right),\; \forall u \in \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right),\; \mathrm{val}\left(\mathrm{coordinateCoupling}\left(r, e, a, z\right), p, u\right) = \mathrm{ite}\left((p = u) \land (\forall b \in \mathrm{Fin}\left(q\right),\; (b \ne \operatorname{Equiv}.\operatorname{symm}\left(a\right)\left(p\right)) \Rightarrow (\mathrm{val}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right)\right), b\right) = \mathrm{val}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right)\right), b\right))), (\mathrm{val}\left(\mathrm{conference}\left(r\right), \mathrm{val}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right)\right), \operatorname{Equiv}.\operatorname{symm}\left(a\right)\left(p\right)\right), \mathrm{val}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right)\right), \operatorname{Equiv}.\operatorname{symm}\left(a\right)\left(p\right)\right)\right):\mathit{Real}), 0\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.coordinateCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is diagonal in the local Majorana index and uses the single coordinate in which the edge endpoints differ.

**Theorem 1.5 (Admissible interactions on the coordinate graph).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right)\right),\; \forall a \in \mathrm{Equiv}\left(\mathrm{Fin}\left(q\right), \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)\right),\; (\mathrm{admissibleEdges}\left(\operatorname{SimpleGraph}.\operatorname{comap}\left(\operatorname{coordinateGraph}\left(q, \operatorname{Index}\left(r\right)\right), e\right), \operatorname{coordinateCoupling}\left(r, e, a\right)\right)) \land (\forall z \in \operatorname{SimpleGraph}.\operatorname{edgeSet}\left(\operatorname{SimpleGraph}.\operatorname{comap}\left(\operatorname{coordinateGraph}\left(q, \operatorname{Index}\left(r\right)\right), e\right)\right),\; \exists t \in \mathrm{Fin}\left(q\right),\; (\mathrm{val}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right)\right), t\right) \ne \mathrm{val}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right)\right), t\right)) \land (\mathrm{coordinateCoupling}\left(r, e, a, z\right) = \operatorname{Matrix}.\operatorname{single}\left(\mathrm{val}\left(a, t\right), \mathrm{val}\left(a, t\right), (\mathrm{val}\left(\mathrm{conference}\left(r\right), \mathrm{val}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right)\right), t\right), \mathrm{val}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Sym2}.\operatorname{out}\left(\operatorname{Subtype}.\operatorname{val}\left(z\right)\right)\right)\right), t\right)\right):\mathit{Real})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.coordinate_edges_admissible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual coordinate edge has one signed coefficient, giving a Hermitian involution with operator norm one and even total parity.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.admissibleEdges`
- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.averagedHamiltonian`
- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.coordinateCoupling`
- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.coordinate_edges_admissible`
- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.quadraticEdge`
- Dependency: [D5/S3/Quantum/Fermionic/CompleteCartesianGraph](CompleteCartesianGraph.md)
- Dependency: [D5/S3/Quantum/Fermionic/ConferenceMatrices](ConferenceMatrices.md)
- Dependency: [D5/S3/Quantum/Fermionic/FockMajoranaCarrier](FockMajoranaCarrier.md)
