# The coordinate skew coupling

## Abstract

Coordinate fibers turn the conference coupling into a flat skew matrix.

Nat, Real and Complex denote natural, real and complex numbers. Matrix products are operator products, smul is scalar multiplication, densityValue is the CStarMatrix value of a density, and densityMatrix is its underlying ordinary matrix; ofMatrix and matrixOf are the canonical CStarMatrix equivalence and its inverse. Fin is the finite index type, ProdType(A, B) denotes the product type A × B (Lean A × B), Assignment(N) is Fin(N) → Bool, and numberParity(N) is exp(iπ times the number operator). siteMajorana(n,m,v,p) means majorana(finProdFinEquiv(v,fst(p)),snd(p)) on Assignment(nm). All divisions below are real or complex divisions, as indicated by asReal and asComplex; inv is the corresponding scalar inverse. edgeCard(G) means G.edgeFinset.card, and coordinateCouplingFamily(r,e,a) is the function z ↦ coordinateCoupling(r,e,a,z).

**Definition 1.1 (Coordinate coefficients).**

$$\forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall p \in \mathrm{ProdType}\left(\mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right), \mathrm{Fin}\left(q\right)\right),\; \forall t \in \mathrm{ProdType}\left(\mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right), \mathrm{Fin}\left(q\right)\right),\; \mathrm{val}\left(\mathrm{coordinateSkew}\left(q, r\right), p, t\right) = \mathrm{ite}\left((\mathrm{snd}\left(p\right) = \mathrm{snd}\left(t\right)) \land (\forall b \in \mathrm{Fin}\left(q\right),\; (b \ne \mathrm{snd}\left(p\right)) \Rightarrow (\mathrm{val}\left(\mathrm{fst}\left(p\right), b\right) = \mathrm{val}\left(\mathrm{fst}\left(t\right), b\right))), \mathrm{asReal}\left(\mathrm{val}\left(\mathrm{conference}\left(r\right), \mathrm{val}\left(\mathrm{fst}\left(p\right), \mathrm{snd}\left(p\right)\right), \mathrm{val}\left(\mathrm{fst}\left(t\right), \mathrm{snd}\left(t\right)\right)\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum.coordinateSkew` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A label consists of a vertex and a selected coordinate. Coefficients vanish between different selected coordinates or different complementary fibers.

**Theorem 1.2 (Flat scalar square).**

$$\forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; (\mathrm{transpose}\left(\mathrm{coordinateSkew}\left(q, r\right)\right) = -\mathrm{coordinateSkew}\left(q, r\right)) \land (\mathrm{coordinateSkew}\left(q, r\right) \cdot \mathrm{coordinateSkew}\left(q, r\right) = \mathrm{smul}\left(-\left(\mathrm{asReal}\left(\mathrm{card}\left(\mathrm{Index}\left(r\right)\right)\right) - 1\right), \mathrm{realIdentity}\left(\mathrm{ProdType}\left(\mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right), \mathrm{Fin}\left(q\right)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum.coordinate_skew_flat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The label equivalence separates the selected entry from the complementary fiber. The resulting blocks are conference matrices, so their skewness and scalar square hold simultaneously.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum.coordinateSkew`
- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum.coordinate_skew_flat`
- Dependency: [D5/S3/Quantum/Fermionic/ConferenceMatrices](ConferenceMatrices.md)
