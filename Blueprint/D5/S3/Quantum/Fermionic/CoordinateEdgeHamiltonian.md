# Real quadratic edge interactions

## Abstract

Real conference coefficients realize normalized quadratic coordinate interactions.

Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). An edge has the representative out(z), whose first and second components give its endpoints. coordinateComap(q,r,e) is coordinateGraph(q,Index(r)).comap(e). Equiv(X,Y) is the equivalence type.

**Definition 1.1 (Real quadratic inter-site term).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall v \in \mathrm{Fin}\left(n\right),\; \forall w \in \mathrm{Fin}\left(n\right),\; \forall K \in \mathrm{Matrix}\left(\mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \mathrm{quadraticEdge}\left(v, w, K\right) = \mathrm{ofMatrix}\left(\mathrm{smul}\left(\mathit{imaginaryUnit}, \sum_{p:\mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)}(\sum_{t:\mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)}(\mathrm{smul}\left(\mathrm{asComplex}\left(\mathrm{val}\left(K, p, t\right)\right), \mathrm{siteMajorana}\left(n, m, v, p\right) \cdot \mathrm{siteMajorana}\left(n, m, w, t\right)\right)))\right)\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.quadraticEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real coefficient matrix multiplies the actual Jordan-Wigner Majorana matrices, with the factor i exactly as displayed.

**Definition 1.2 (Literal edge average).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \forall K \in \mathrm{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; \mathrm{averagedHamiltonian}\left(G, K\right) = \mathrm{smul}\left(\mathrm{inv}\left(\mathrm{asReal}\left(\mathrm{edgeCard}\left(G\right)\right)\right), \sum_{z:\mathrm{edgeSet}\left(G\right)}(\mathrm{quadraticEdge}\left(\mathrm{fst}\left(\mathrm{out}\left(z\right)\right), \mathrm{snd}\left(\mathrm{out}\left(z\right)\right), \mathrm{val}\left(K, z\right)\right))\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.averagedHamiltonian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum runs over all actual unordered edges and is multiplied by the reciprocal of their cardinality.

**Definition 1.3 (Interaction admissibility).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall G \in \mathrm{SimpleGraph}\left(\mathrm{Fin}\left(n\right)\right),\; \forall K \in \mathrm{edgeSet}\left(G\right) \to \mathrm{Matrix}\left(\mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right), \mathit{Real}\right),\; (\mathrm{admissibleEdges}\left(G, K\right)) \Leftrightarrow (\forall z \in \mathrm{edgeSet}\left(G\right),\; ((\mathrm{IsSelfAdjoint}\left(\mathrm{quadraticEdge}\left(\mathrm{fst}\left(\mathrm{out}\left(z\right)\right), \mathrm{snd}\left(\mathrm{out}\left(z\right)\right), \mathrm{val}\left(K, z\right)\right)\right)) \land (\left\lVert \mathrm{quadraticEdge}\left(\mathrm{fst}\left(\mathrm{out}\left(z\right)\right), \mathrm{snd}\left(\mathrm{out}\left(z\right)\right), \mathrm{val}\left(K, z\right)\right) \right\rVert \le 1)) \land (\mathrm{Commute}\left(\mathrm{quadraticEdge}\left(\mathrm{fst}\left(\mathrm{out}\left(z\right)\right), \mathrm{snd}\left(\mathrm{out}\left(z\right)\right), \mathrm{val}\left(K, z\right)\right), \mathrm{ofMatrix}\left(\mathrm{numberParity}\left(n \cdot m\right)\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.admissibleEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Admissibility means Hermitian, operator norm at most one, and commutation with total occupation parity on each edge.

**Definition 1.4 (Conference edge coefficients).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right)\right),\; \forall a \in \mathrm{Equiv}\left(\mathrm{Fin}\left(q\right), \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)\right),\; \forall z \in \mathrm{edgeSet}\left(\mathrm{coordinateComap}\left(q, r, e\right)\right),\; \forall p \in \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right),\; \forall u \in \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right),\; \mathrm{val}\left(\mathrm{coordinateCoupling}\left(r, e, a, z\right), p, u\right) = \mathrm{ite}\left((p = u) \land (\forall b \in \mathrm{Fin}\left(q\right),\; (b \ne \mathrm{equivInverse}\left(a, p\right)) \Rightarrow (\mathrm{val}\left(\mathrm{val}\left(e, \mathrm{fst}\left(\mathrm{out}\left(z\right)\right)\right), b\right) = \mathrm{val}\left(\mathrm{val}\left(e, \mathrm{snd}\left(\mathrm{out}\left(z\right)\right)\right), b\right))), \mathrm{asReal}\left(\mathrm{val}\left(\mathrm{conference}\left(r\right), \mathrm{val}\left(\mathrm{val}\left(e, \mathrm{fst}\left(\mathrm{out}\left(z\right)\right)\right), \mathrm{equivInverse}\left(a, p\right)\right), \mathrm{val}\left(\mathrm{val}\left(e, \mathrm{snd}\left(\mathrm{out}\left(z\right)\right)\right), \mathrm{equivInverse}\left(a, p\right)\right)\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian.coordinateCoupling` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient is diagonal in the local Majorana index and uses the single coordinate in which the edge endpoints differ.

**Theorem 1.5 (Admissible interactions on the coordinate graph).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right)\right),\; \forall a \in \mathrm{Equiv}\left(\mathrm{Fin}\left(q\right), \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)\right),\; (\mathrm{admissibleEdges}\left(\mathrm{coordinateComap}\left(q, r, e\right), \mathrm{coordinateCouplingFamily}\left(r, e, a\right)\right)) \land (\forall z \in \mathrm{edgeSet}\left(\mathrm{coordinateComap}\left(q, r, e\right)\right),\; \exists t \in \mathrm{Fin}\left(q\right),\; (\mathrm{val}\left(\mathrm{val}\left(e, \mathrm{fst}\left(\mathrm{out}\left(z\right)\right)\right), t\right) \ne \mathrm{val}\left(\mathrm{val}\left(e, \mathrm{snd}\left(\mathrm{out}\left(z\right)\right)\right), t\right)) \land (\mathrm{coordinateCoupling}\left(r, e, a, z\right) = \mathrm{matrixSingle}\left(\mathrm{val}\left(a, t\right), \mathrm{val}\left(a, t\right), \mathrm{asReal}\left(\mathrm{val}\left(\mathrm{conference}\left(r\right), \mathrm{val}\left(\mathrm{val}\left(e, \mathrm{fst}\left(\mathrm{out}\left(z\right)\right)\right), t\right), \mathrm{val}\left(\mathrm{val}\left(e, \mathrm{snd}\left(\mathrm{out}\left(z\right)\right)\right), t\right)\right)\right)\right)))$$

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
