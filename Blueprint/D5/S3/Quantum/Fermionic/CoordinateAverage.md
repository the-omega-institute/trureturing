# Identifying the edge average

## Abstract

The literal unordered edge average equals the flat coordinate Clifford operator.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Theorem 1.1 (The factor of two in the dense Clifford sum).**

$$\forall n \in \mathit{Nat},\; \forall m \in \mathit{Nat},\; \forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall e \in \mathrm{Equiv}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right)\right),\; \forall a \in \mathrm{Equiv}\left(\mathrm{Fin}\left(q\right), \operatorname{Prod}\left(\mathrm{Fin}\left(m\right), \mathit{Bool}\right)\right),\; \operatorname{Equiv}.\operatorname{symm}\left(\operatorname{CStarMatrix}.\operatorname{ofMatrix}\right)\left(\mathrm{averagedHamiltonian}\left(\operatorname{SimpleGraph}.\operatorname{comap}\left(\operatorname{coordinateGraph}\left(q, \operatorname{Index}\left(r\right)\right), e\right), \operatorname{coordinateCoupling}\left(r, e, a\right)\right)\right) = \operatorname{SMul}.\operatorname{smul}\left(\operatorname{Inv}.\operatorname{inv}\left((\operatorname{Finset}.\operatorname{card}\left(\operatorname{SimpleGraph}.\operatorname{edgeFinset}\left(\operatorname{SimpleGraph}.\operatorname{comap}\left(\operatorname{coordinateGraph}\left(q, \operatorname{Index}\left(r\right)\right), e\right)\right)\right):\mathit{Real})\right), \operatorname{SMul}.\operatorname{smul}\left(\frac{\operatorname{Complex}.\operatorname{I}}{2}, \sum_{p:\operatorname{Prod}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right)\right)}(\sum_{t:\operatorname{Prod}\left(\mathrm{Fin}\left(n\right), \mathrm{Fin}\left(q\right)\right)}(\operatorname{SMul}.\operatorname{smul}\left((\mathrm{val}\left(\mathrm{coordinateSkew}\left(q, r\right), \operatorname{Prod}.\operatorname{mk}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{fst}\left(p\right)\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right), \operatorname{Prod}.\operatorname{mk}\left(\mathrm{val}\left(e, \operatorname{Prod}.\operatorname{fst}\left(t\right)\right), \operatorname{Prod}.\operatorname{snd}\left(t\right)\right)\right):\mathit{Complex}), \operatorname{majorana}\left(n \cdot m, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{fst}\left(\mathrm{val}\left(a, \operatorname{Prod}.\operatorname{snd}\left(p\right)\right)\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\mathrm{val}\left(a, \operatorname{Prod}.\operatorname{snd}\left(p\right)\right)\right)\right) \cdot \operatorname{majorana}\left(n \cdot m, \operatorname{finProdFinEquiv}\left(\operatorname{Prod}.\operatorname{mk}\left(\operatorname{Prod}.\operatorname{fst}\left(t\right), \operatorname{Prod}.\operatorname{fst}\left(\mathrm{val}\left(a, \operatorname{Prod}.\operatorname{snd}\left(t\right)\right)\right)\right)\right), \operatorname{Prod}.\operatorname{snd}\left(\mathrm{val}\left(a, \operatorname{Prod}.\operatorname{snd}\left(t\right)\right)\right)\right)\right)))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CoordinateAverage.coordinate_average` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every unordered coordinate edge has two orientations. Skewness of its real coefficient cancels the sign from reversing its two Majoranas, so the dense double sum counts its interaction twice. The identity keeps the literal reciprocal edge count.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateAverage.coordinate_average`
- Dependency: [D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum](CoordinateCliffordSpectrum.md)
- Dependency: [D5/S3/Quantum/Fermionic/CoordinateEdgeHamiltonian](CoordinateEdgeHamiltonian.md)
