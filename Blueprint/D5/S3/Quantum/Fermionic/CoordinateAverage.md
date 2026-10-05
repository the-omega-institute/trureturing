# Identifying the edge average

## Abstract

The literal unordered edge average equals the flat coordinate Clifford operator.

Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z). coordinateComap(q,r,e) is coordinateGraph(q,Index(r)).comap(e). The vertex enumeration e transports Fin(n) to the actual coordinate vertices, and a identifies the coordinate indices with the local Majorana indices.

**Theorem 1.1 (The factor of two in the dense Clifford sum).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right)\right),\; \forall a \in \mathrm{Equiv}\left(\mathrm{Fin}\left(q\right), \mathrm{ProdType}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)\right),\; \mathrm{matrixOf}\left(\mathrm{averagedHamiltonian}\left(\mathrm{coordinateComap}\left(q, r, e\right), \mathrm{coordinateCouplingFamily}\left(r, e, a\right)\right)\right) = \mathrm{smul}\left(\mathrm{inv}\left(\mathrm{asReal}\left(\mathrm{edgeCard}\left(\mathrm{coordinateComap}\left(q, r, e\right)\right)\right)\right), \mathrm{smul}\left(\frac{\mathit{imaginaryUnit}}{2}, \sum_{p:\mathrm{ProdType}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right)\right)}(\sum_{t:\mathrm{ProdType}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right)\right)}(\mathrm{smul}\left(\mathrm{asComplex}\left(\mathrm{val}\left(\mathrm{coordinateSkew}\left(q, r\right), \mathrm{pair}\left(\mathrm{val}\left(e, \mathrm{fst}\left(p\right)\right), \mathrm{snd}\left(p\right)\right), \mathrm{pair}\left(\mathrm{val}\left(e, \mathrm{fst}\left(t\right)\right), \mathrm{snd}\left(t\right)\right)\right)\right), \mathrm{siteMajorana}\left(n, m, \mathrm{fst}\left(p\right), \mathrm{val}\left(a, \mathrm{snd}\left(p\right)\right)\right) \cdot \mathrm{siteMajorana}\left(n, m, \mathrm{fst}\left(t\right), \mathrm{val}\left(a, \mathrm{snd}\left(t\right)\right)\right)\right)))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CoordinateAverage.coordinate_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unordered coordinate edge has two orientations. Skewness of its real coefficient cancels the sign from reversing its two Majoranas, so the dense double sum counts its interaction twice. The identity keeps the literal reciprocal edge count.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateAverage.coordinate_average`
- Dependency: [D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum](CoordinateCliffordSpectrum.md)
- Dependency: [D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian](CoordinateEdgeHamiltonian.md)
