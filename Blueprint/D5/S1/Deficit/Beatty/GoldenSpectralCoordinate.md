# Golden Spectral Coordinate

## Abstract

Golden-square scaling sends the structural zero to one half, and the centered spectral coordinate is real exactly on the structural line.

**Definition 1.1 (Golden eigenvalue).**

$$\varphi = \frac{1 + \sqrt{5}}{2}$$

*Formalization.* `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.phi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The value phi=(1+sqrt(5))/2 is transcribed verbatim from D5/X_Frontier/Hearts.lean. This module does not import that frozen frontier owner.

**Definition 1.2 (Structural pole).**

$$\operatorname{structuralPole} = \frac{1}{\varphi^{3}}$$

*Formalization.* `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.structuralPole` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structural pole 1/phi^3 is transcribed with the same bytes of mathematical content as the frontier route, without importing it.

**Definition 1.3 (Structural zero).**

$$\operatorname{structuralZero} = \frac{1}{2 \cdot \varphi^{2}}$$

*Formalization.* `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.structuralZero` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The structural zero is the reciprocal of twice phi squared, again transcribed verbatim from the route's frozen frontier constants.

**Definition 1.4 (Golden natural scale).**

$$\forall s \in \mathbb{C},\; \operatorname{goldenNaturalScale}(s) = \varphi^{2} \cdot s$$

*Formalization.* `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.goldenNaturalScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural scale multiplies a complex variable by the real scalar phi squared. Its named one-half instantiation below makes this definition earn its freeze.

**Definition 1.5 (Golden spectral parameter).**

$$\forall s \in \mathbb{C},\; \operatorname{goldenSpectralParameter}(s) = -i \cdot {\operatorname{goldenNaturalScale}(s) - \frac{1}{2}}$$

*Formalization.* `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.goldenSpectralParameter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The spectral parameter rotates the centered natural scale by minus i. The independent real-spectrum equivalence below makes this definition earn its freeze.

**Theorem 1.6 (Golden natural scaling hits one half).**

$$\operatorname{goldenNaturalScale}(\operatorname{structuralZero}) = \frac{1}{2}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.golden_natural_scale_hits_half` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the structural zero, multiplication by phi squared cancels the reciprocal phi square and leaves exactly one half. This is route obligation R-A.

**Theorem 1.7 (The golden spectral parameter is real exactly on the structural line).**

$$\forall s \in \mathbb{C},\; \operatorname{Im}(\operatorname{goldenSpectralParameter}(s)) = 0 \Leftrightarrow \operatorname{Re}(s) = \operatorname{structuralZero}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.golden_spectral_im_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every complex s, expanding complex multiplication gives imaginary part minus (phi squared times Re(s) minus one half). Positivity of phi permits cancellation, so it vanishes exactly at structuralZero.

This iff is route obligation R-C. Together with the R-A instantiation, it is the freeze-earning content for the two new coordinate definitions; neither theorem is a definitional tautology.

The consumer transports the O-5 line into the existing CriticalLine and off-line orbit language. The classical analogue is D5/S3/Weil/ZetaBridge/ConvolutionSquareCriticalLine; it is named here for comparison and is deliberately not imported.

Exact repository and pinned-Mathlib searches found no whole target. Mathlib supplies the golden-ratio bound, complex component laws, and nonzero cancellation used in the proof.

## References

- Truth anchor: `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.goldenNaturalScale`
- Truth anchor: `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.goldenSpectralParameter`
- Truth anchor: `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.golden_natural_scale_hits_half`
- Truth anchor: `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.golden_spectral_im_eq_zero_iff`
- Truth anchor: `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.phi`
- Truth anchor: `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.structuralPole`
- Truth anchor: `D5/S1/Deficit/Beatty/GoldenSpectralCoordinate.structuralZero`
