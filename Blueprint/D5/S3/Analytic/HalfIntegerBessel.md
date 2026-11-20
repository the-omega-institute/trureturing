# Complex half-integer modified Bessel carriers

## Abstract

The finite complex half-integer carriers and their Wronskians on the right half-plane.

**Definition 1.1 (Common prefactor).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.prefactor`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.prefactor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The common prefactor is the positive real square root of pi/2 divided by the principal complex square root of z.

**Definition 1.2 (Decaying carrier).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.K`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.K` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

At order m+1/2, K is the prefactor times exp(-z) times P_m(1/z), where P_m is the rational factorial polynomial.

**Definition 1.3 (Reflected carrier).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.L`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.L` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The growing carrier is the prefactor times exp(z) times P_m(-1/z).

**Definition 1.4 (Regular carrier).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.I`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.I` (`✓ std3`).

*Citation.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The regular carrier I is the difference of L and (-1)^m K divided by pi.

**Theorem 1.5 (Derivative of the decaying carrier).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re z > 0 the derivative of K is its prefactor times exp(-z) times the sum of -(1+1/(2z)) P_m(1/z) and -P_m'(1/z)/z^2.

**Theorem 1.6 (Derivative of the reflected carrier).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_L`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_L` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re z > 0 the derivative of L is its prefactor times exp(z) times the sum of (1-1/(2z)) Q_m(1/z) and -Q_m'(1/z)/z^2, where Q_m(X) = P_m(-X).

**Theorem 1.7 (Derivative of the regular carrier).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_I`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_I` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re z > 0 the derivative of I is (L' - (-1)^m K')/pi.

**Theorem 1.8 (Wronskian of the finite reflected pair).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.wronskian_KL`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.wronskian_KL` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re z > 0, z(K L' - K' L) = pi. The square-root terms cancel in the derivative difference. Evaluating the rational reflected Wronskian at 1/z gives the factor 2, and the squared prefactor is pi/(2z).

**Theorem 1.9 (Wronskian of the decaying and regular carriers).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.wronskian_KI`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.wronskian_KI` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

On Re z > 0, K I' - K' I = 1/z. The multiple of K cancels and the reflected Wronskian is divided by pi.

**Theorem 1.10 (Ordinary modified Bessel equation).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_deriv_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_deriv_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

At order nu = m+1/2 and on Re z > 0, the derivative of K' is (1+nu^2/z^2) K - K'/z. Differentiating the finite carrier twice reduces the equation to the rational polynomial equation at 1/z.

## References

- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.I`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.L`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_I`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_L`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_deriv_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.prefactor`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.wronskian_KI`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.wronskian_KL`
- Dependency: [D5/S3/Analytic/HalfIntegerBesselPolynomial](HalfIntegerBesselPolynomial.md)
