# Golden Exponential Prony Coordinate

## Abstract

The split golden sampling atom is a nonvanishing complex character: addition of lifted displacements becomes multiplication of Prony nodes, natural translation becomes powers, and radius records the real displacement.

**Theorem 1.1 (The complex coordinate equals the existing golden sampling atom).**

$$\forall z, \operatorname{goldenExponentialPronyCoordinate}(z) = \operatorname{goldenSamplingAtom}(\operatorname{im}(z), \operatorname{re}(z)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.golden_exponential_prony_coordinate_eq_sampling_atom` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Packaging a complex displacement by its real and imaginary parts reproduces the repository's existing radial-phase golden sampling atom exactly.

This theorem prevents a second sampling convention and fixes the sign of both radial damping and phase rotation.

**Theorem 1.2 (Lifted addition becomes multiplication of Prony nodes).**

$$\forall z, \forall w, \operatorname{goldenExponentialPronyCoordinate}(z + w) = \operatorname{goldenExponentialPronyCoordinate}(z) \cdot \operatorname{goldenExponentialPronyCoordinate}(w).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.golden_exponential_prony_coordinate_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden exponential coordinate is an additive-to-multiplicative character on the lifted complex displacement plane.

Consequently, independent shifts compose without introducing a second transport law.

**Theorem 1.3 (Natural translation depth becomes ordinary powers).**

$$\forall t, \forall z, \operatorname{goldenExponentialPronyCoordinate}(t \cdot z) = \operatorname{goldenExponentialPronyCoordinate}(z)^{t}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.golden_exponential_prony_coordinate_nat_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sampling a lifted displacement after a natural number of equal steps gives the corresponding ordinary power of the one-step node.

This is the exact time-character law required by finite Prony and Vandermonde reconstruction.

**Theorem 1.4 (Node equality preserves radial displacement).**

$$\forall z, \forall w, \operatorname{goldenExponentialPronyCoordinate}(z) = \operatorname{goldenExponentialPronyCoordinate}(w) \Rightarrow \operatorname{re}(z) = \operatorname{re}(w).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.golden_exponential_prony_coordinate_eq_implies_re_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equal golden exponential nodes have equal real coordinates because their norms are injective real exponentials of the radial displacement.

Any unresolved collision is therefore purely vertical phase aliasing. No global imaginary-direction injectivity is claimed.

## References

- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.golden_exponential_prony_coordinate_add`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.golden_exponential_prony_coordinate_eq_implies_re_eq`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.golden_exponential_prony_coordinate_eq_sampling_atom`
- Truth anchor: `D5/S3/Weil/GoldenCriticalSpectrum/GoldenExponentialPronyCoordinate.golden_exponential_prony_coordinate_nat_mul`
- Dependency: [D5/S3/Weil/GoldenCriticalSpectrum/GoldenSamplingAtom](GoldenSamplingAtom.md)
