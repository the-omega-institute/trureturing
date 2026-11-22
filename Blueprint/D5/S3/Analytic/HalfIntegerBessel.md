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

**Definition 1.11 (Real order).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.order`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.order` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The order nu is m + 1/2.

**Definition 1.12 (Phase root).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.S`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.S` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

S(w) is the principal square root of 1 + w^2.

**Theorem 1.13 (Sign of the phase root).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.S_re_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.S_re_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If Re w > 0, then Re S(w) > 0. The radicand lies in the slit plane.

**Definition 1.14 (Phase).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.eta`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.eta` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The phase is S(w) + Log w - Log(1 + S(w)), with principal logarithms.

**Theorem 1.15 (Principal logarithm of the phase quotient).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.eta_eq_log_div`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.eta_eq_log_div` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re w > 0 the phase is S(w) + Log(w / (1 + S(w))).

**Theorem 1.16 (Phase derivative).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_eta`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_eta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re w > 0 the derivative of the phase is S(w) / w.

**Theorem 1.17 (Principal square root under positive scaling).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.sqrt_real_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.sqrt_real_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a > 0 and Re w > 0, the principal root of a w equals the real root of a times the principal root of w.

**Definition 1.18 (Normalized decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.F_K`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.F_K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

F_K is sqrt(2 nu / pi) sqrt(S(w)) exp(nu eta(w)) K_m(nu w). The first root is real and the second is principal complex.

**Theorem 1.19 (Canceled normalization of the decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.F_K_eq_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.F_K_eq_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re w > 0, F_K is sqrt(S(w)) / sqrt(w) times exp(nu (eta(w) - w)) times P_m(1 / (nu w)). Positive real scaling factors out of the principal root.

**Definition 1.20 (Phase differentiation).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.D`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D applies the complex derivative and multiplies by w / S(w).

**Definition 1.21 (Liouville–Green potential).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.psi`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The potential is w^2 (4 - w^2) / (4 (1 + w^2)^3).

**Theorem 1.22 (Scaled equation for the decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.liouvilleGreen_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.liouvilleGreen_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

On Re w > 0, D^2 F_K - 2 nu D F_K = psi F_K. The scaled ordinary equation for K_m first gives D^2 U = (nu^2 + psi) U for U = sqrt(S(w)) K_m(nu w). The exponential factor gives the equation for F_K.

## References

- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.D`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.F_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.F_K_eq_carrier`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.I`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.L`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.S`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.S_re_pos`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.eta`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.eta_eq_log_div`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_I`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_L`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_deriv_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.hasDerivAt_eta`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.liouvilleGreen_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.order`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.prefactor`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.psi`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.sqrt_real_mul`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.wronskian_KI`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.wronskian_KL`
- Dependency: [D5/S3/Analytic/HalfIntegerBesselPolynomial](HalfIntegerBesselPolynomial.md)
