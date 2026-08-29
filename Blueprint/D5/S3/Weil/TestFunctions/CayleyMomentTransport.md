# Cayley Moment Transport

## Abstract

Resolvent weighting and the Cayley map transport local Fourier moments to the circle.

**Definition 1.1 (Positive-scale Cayley map).**

Lean statement: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyCircle`

*Formalization.* `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyCircle` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real resolvent Cayley character is bundled on the exact complex unit circle. Positivity of the scale supplies the nonvanishing denominator.

**Definition 1.2 (Resolvent density).**

Lean statement: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.resolventDensity`

*Formalization.* `D5/S3/Weil/TestFunctions/CayleyMomentTransport.resolventDensity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The positive density is the reciprocal of xi squared plus the scale squared.

**Definition 1.3 (Resolvent Cayley compactification).**

Lean statement: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyCompactification`

*Formalization.* `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyCompactification` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive real-line measure is weighted by the resolvent density and pushed forward through the positive-scale Cayley map.

**Definition 1.4 (Cayley inverse coordinate).**

Lean statement: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyInverse`

*Formalization.* `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real part of the inverse fractional-linear coordinate recovers the real spectral parameter away from the omitted circle point.

**Definition 1.5 (Cayley local moment function).**

Lean statement: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyMomentFunction`

*Formalization.* `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyMomentFunction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local circle observable multiplies the Fourier-Laplace transform by the resolvent denominator and takes value zero at the omitted point.

**Definition 1.6 (Inverse-measure pairing).**

Lean statement: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.inverseMeasurePairing`

*Formalization.* `D5/S3/Weil/TestFunctions/CayleyMomentTransport.inverseMeasurePairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The pairing is the real-line integral of the local Fourier-Laplace transform against the supplied positive measure.

**Theorem 1.7 (Local Fourier moments transport through Cayley compactification).**

$$\forall a \in \operatorname{Real}\left(\right), nu \in \operatorname{Measure}\left(\operatorname{Real}\left(\right)\right), phi \in \operatorname{WeilTestFunction}\left(\right),\; 0 < a \Rightarrow \left(\operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{cayleyMomentFunction}\left(a, phi, z\right), \operatorname{cayleyCompactification}\left(a, nu\right)\right) = \operatorname{integral}\left(xi, \operatorname{Real}\left(\right), \operatorname{fourierLaplace}\left(phi, xi\right), nu\right) \land \left(\operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{cayleyMomentFunction}\left(a, phi, z\right), \operatorname{cayleyCompactification}\left(a, nu\right)\right) = \operatorname{inverseMeasurePairing}\left(nu, phi\right) \land \operatorname{integral}\left(z, \operatorname{Circle}\left(\right), \operatorname{cayleyMomentFunction}\left(a, phi, z\right), \operatorname{normalizedCircleHaar}\left(\right)\right) = \operatorname{complex}\left(2 \cdot a\right) \cdot phi\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayley_moment_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive scale, real-line measure, and Weil test function, the compactified circle moment equals the real Fourier moment and the named inverse-measure pairing.

The normalized circle Haar moment is also public and equals twice the scale times the value of the test function at zero. The proof uses the one-dimensional Cayley Jacobian and Schwartz Fourier inversion in the repository convention.

## References

- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyCircle`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyCompactification`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyInverse`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayleyMomentFunction`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.cayley_moment_transport`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.inverseMeasurePairing`
- Truth anchor: `D5/S3/Weil/TestFunctions/CayleyMomentTransport.resolventDensity`
- Dependency: [D5/S3/Weil/Budget/FullCirclePrimalAttainment](../Budget/FullCirclePrimalAttainment.md)
- Dependency: [D5/S3/Weil/TestFunctions/CayleyLaguerreMomentTomography](CayleyLaguerreMomentTomography.md)
- Dependency: [D5/S3/Weil/TestFunctions/ConvolutionSquarePositivity](ConvolutionSquarePositivity.md)
