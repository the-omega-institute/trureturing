# The prescribed rational inverse series

## Abstract

The rational arcsine coefficients specify a unique formal inverse; analytic endpoint convergence is a further obligation.

**Definition 1.1 (Rational coefficients in every degree).**

$$\forall n \in Nat,\; \operatorname{alpha}\left(2n\right) = 0 \land \operatorname{alpha}\left(2n + 1\right) = \operatorname{div}\left(\operatorname{choose}\left(2n, n\right), 4^{n}(2n + 1)\right)$$

*Formalization.* `D5/S3/Analytic/PowerSeries/DottieInverseSeries.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coefficient sequence alpha takes values in the rationals. Its even coefficients vanish and its degree 2n+1 coefficient is choose(2n,n)/(4^n(2n+1)). The definition selects these cases using the parity and integer half of the input degree.

**Definition 1.2 (The formal rational arcsine series).**

$$S = \operatorname{mk}\left(\operatorname{alpha}\left(\right)\right)$$

*Formalization.* `D5/S3/Analytic/PowerSeries/DottieInverseSeries.arcsine` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

S denotes PowerSeries.mk alpha over the rationals. Its coefficient in degree zero is zero.

**Definition 1.3 (The forward series).**

$$A = 2X + 2S$$

*Formalization.* `D5/S3/Analytic/PowerSeries/DottieInverseSeries.forward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A is the literal rational formal series 2X+2S. Its constant coefficient is zero and its linear coefficient is 4, a unit in the rational field.

**Definition 1.4 (The prescribed formal inverse).**

$$B = \operatorname{substInvOfIsUnit}\left(A, \operatorname{unit}\left(4\right)\right)$$

*Formalization.* `D5/S3/Analytic/PowerSeries/DottieInverseSeries.inverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B is exactly A.substInvOfIsUnit for the proof that the linear coefficient 4 is a unit. The choice of that proof does not alter the formal series.

## Connecting an analytic inverse

For a complex function H analytic at zero and real on the real axis near zero, let h(y)=Re(H(y)) for real y. The real_taylor_data lemma supplies real analyticity of h and the real and imaginary parts of every complex derivative coefficient, including degree zero. Its Taylor series T has coefficient iteratedDeriv(n,h,0)/n!.

Suppose H(0)=0, the real function a(x)=2x+2arcsin(x) has the expansion given by A mapped to the reals, and a(h(y))=y near zero. Then T has zero constant coefficient. The scalar composition correspondence identifies the expansion of a composed with h with the realization of A substituted by T. Uniqueness of one-dimensional analytic expansions makes that substitution equal X. The mapped rational series B is another right formal inverse, by map_subst. Formal inverse uniqueness therefore gives T equal to B mapped to the reals. The same real_taylor_data coefficients then identify every complex derivative coefficient of H with the complex image of the corresponding rational coefficient of B.

These local analytic and inverse-germ premises require proof for a selected H. A common analytic inverse on a disk of radius greater than pi, real preservation, the exact arcsine germ, and its selected value at pi remain necessary to establish absolute summability at pi and identify its sum. No endpoint convergence or cosine fixed-point value is asserted here.

## References

- Truth anchor: `D5/S3/Analytic/PowerSeries/DottieInverseSeries.alpha`
- Truth anchor: `D5/S3/Analytic/PowerSeries/DottieInverseSeries.arcsine`
- Truth anchor: `D5/S3/Analytic/PowerSeries/DottieInverseSeries.forward`
- Truth anchor: `D5/S3/Analytic/PowerSeries/DottieInverseSeries.inverse`
- Dependency: [D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis](../Fourier/PositiveDefiniteImaginaryAxis.md)
- Dependency: [D5/S3/Analytic/PowerSeries/ScalarComposition](ScalarComposition.md)
