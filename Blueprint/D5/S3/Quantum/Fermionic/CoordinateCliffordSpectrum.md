# The coordinate skew coupling

## Abstract

Coordinate fibers turn the conference coupling into a flat skew matrix.

Natural subtraction is truncated at zero. All other divisions are in Real or Complex. Scalar casts retain their target type. Matrix products are operator products, and Matrix.conjTranspose is conjugate transpose. Subtype.val is the value of a density; Equiv.symm applied to CStarMatrix.ofMatrix recovers its ordinary matrix. Assignment N is the occupation basis Fin N → Bool. Implicit Lean mode and dimension arguments may be displayed explicitly. Bracketed Fintype, DecidableEq and Nonempty assumptions are anonymous instance arguments.

**Definition 1.1 (Coordinate coefficients).**

$$\forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; \forall p \in \operatorname{Prod}\left(\mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right), \mathrm{Fin}\left(q\right)\right),\; \forall t \in \operatorname{Prod}\left(\mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right), \mathrm{Fin}\left(q\right)\right),\; \mathrm{val}\left(\mathrm{coordinateSkew}\left(q, r\right), p, t\right) = \mathrm{ite}\left((\operatorname{Prod}.\operatorname{snd}\left(p\right) = \operatorname{Prod}.\operatorname{snd}\left(t\right)) \land (\forall b \in \mathrm{Fin}\left(q\right),\; (b \ne \operatorname{Prod}.\operatorname{snd}\left(p\right)) \Rightarrow (\mathrm{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right), b\right) = \mathrm{val}\left(\operatorname{Prod}.\operatorname{fst}\left(t\right), b\right))), (\mathrm{val}\left(\mathrm{conference}\left(r\right), \mathrm{val}\left(\operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right), \mathrm{val}\left(\operatorname{Prod}.\operatorname{fst}\left(t\right), \operatorname{Prod}.\operatorname{snd}\left(t\right)\right)\right):\mathit{Real}), 0\right)$$

*Formalization.* `D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum.coordinateSkew` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A label consists of a vertex and a selected coordinate. Coefficients vanish between different selected coordinates or different complementary fibers.

**Theorem 1.2 (Flat scalar square).**

$$\forall q \in \mathit{Nat},\; \forall r \in \mathit{Nat},\; (\operatorname{Matrix}.\operatorname{transpose}\left(\mathrm{coordinateSkew}\left(q, r\right)\right) = -\mathrm{coordinateSkew}\left(q, r\right)) \land (\mathrm{coordinateSkew}\left(q, r\right) \cdot \mathrm{coordinateSkew}\left(q, r\right) = \operatorname{SMul}.\operatorname{smul}\left(-\left((\operatorname{Fintype}.\operatorname{card}\left(\mathrm{Index}\left(r\right)\right):\mathit{Real}) - 1\right), (1:\operatorname{Matrix}\left(\operatorname{Prod}\left(\mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right), \mathrm{Fin}\left(q\right)\right), \operatorname{Prod}\left(\mathrm{Fin}\left(q\right) \to \mathrm{Index}\left(r\right), \mathrm{Fin}\left(q\right)\right), \mathit{Real}\right))\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum.coordinate_skew_flat` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The label equivalence separates the selected entry from the complementary fiber. The resulting blocks are conference matrices, so their skewness and scalar square hold simultaneously.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum.coordinateSkew`
- Truth anchor: `D5/S3/Quantum/Fermionic/CoordinateCliffordSpectrum.coordinate_skew_flat`
- Dependency: [D5/S3/Quantum/Fermionic/ConferenceMatrices](ConferenceMatrices.md)
