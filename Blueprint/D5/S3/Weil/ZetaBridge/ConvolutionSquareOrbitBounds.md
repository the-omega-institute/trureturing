# Convolution-Square Orbit Energy Bounds

## Abstract

Complex-frequency convolution-square factorization gives an energy bound for every off-line four-point zero orbit, without assigning an off-line sign.

**Theorem 1.1 (Complex-frequency convolution-square factorization).**

$$\forall g\in \mathcal{W}, \forall z\in \mathbb{C}, \operatorname{fourierLaplace} \operatorname{convolutionSquare}(g)(z) = \operatorname{fourierLaplace} g (z)\cdot \overline{\operatorname{fourierLaplace} g (\overline{z})}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds.fourierLaplace_convolutionSquare_complex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twist g and its Weil involution by the complex exponential kernel. The kernel is multiplicative under addition, so the twisted convolution is the kernel times convolutionSquare g. Mathlib's integral_convolution then factors the integral, and fourierLaplace_involution_conj identifies the second factor with the conjugated transform at the conjugate frequency.

**Theorem 1.2 (An off-line orbit real value is bounded by transform energy).**

$$\forall Z: \operatorname{ZeroData}, g\in \mathcal{W}, n\in \mathbb{N}, Z.conjugation(n) \neq n \land \Re(Z.zero(n)) \neq \operatorname{criticalAbscissa} \Rightarrow \neg(energyBound) \leq \Re(\operatorname{orbitSum}(Z,g,n)) \land \Re(\operatorname{orbitSum}(Z,g,n)) \leq energyBound)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds.off_line_zero_orbit_sum_energy_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four-point orbit identity makes the orbit total four times the real part of one multiplicity-weighted summand. Factorization writes its transform as A times the conjugate of B, with A and B evaluated at gamma and its conjugate. Complex.normSq_add and Complex.normSq_sub give the two-sided AM-GM estimate, yielding energyBound = 2 times multiplicity times (normSq A + normSq B). This records no sign or positivity for off-line terms.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds.fourierLaplace_convolutionSquare_complex`
- Truth anchor: `D5/S3/Weil/ZetaBridge/ConvolutionSquareOrbitBounds.off_line_zero_orbit_sum_energy_bounds`
- Dependency: [D5/S3/Weil/ZetaBridge/ConvolutionSquareOffLineOrbits](ConvolutionSquareOffLineOrbits.md)
