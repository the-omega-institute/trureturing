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

**Definition 1.17 (Normalized decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.F_K`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.F_K` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

F_K is sqrt(2 nu / pi) sqrt(S(w)) exp(nu eta(w)) K_m(nu w). The first root is real and the second is principal complex.

**Theorem 1.18 (Canceled normalization of the decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.F_K_eq_carrier`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.F_K_eq_carrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re w > 0, F_K is sqrt(S(w)) / sqrt(w) times exp(nu (eta(w) - w)) times P_m(1 / (nu w)). Positive real scaling factors out of the principal root.

**Definition 1.19 (Phase differentiation).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.D`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D applies the complex derivative and multiplies by w / S(w).

**Definition 1.20 (Liouville–Green potential).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.psi`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.psi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The potential is w^2 (4 - w^2) / (4 (1 + w^2)^3).

**Theorem 1.21 (Scaled equation for the decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.liouvilleGreen_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.liouvilleGreen_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

On Re w > 0, D^2 F_K - 2 nu D F_K = psi F_K. The scaled ordinary equation for K_m first gives D^2 U = (nu^2 + psi) U for U = sqrt(S(w)) K_m(nu w). The exponential factor gives the equation for F_K.

**Definition 1.22 (Radial phase coefficient).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.radialP`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.radialP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the ray r u, p(r) is S(r u) / r.

**Definition 1.23 (Radial potential coefficient).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.radialQ`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.radialQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the ray, q(r) is p(r) psi(r u).

**Theorem 1.24 (Radial system for the decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.radialSystem_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.radialSystem_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re u > 0 and r > 0, eta(r u) has derivative p(r). With F(r) = F_K(r u) and G(r) = (D F_K)(r u), the real derivatives are F' = p G and G' = 2 nu p G + q F. Also Re p > 0.

**Theorem 1.25 (Sector angle of the phase root).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.radial_S_re_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.radial_S_re_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If u has unit norm and positive real part and r > 0, then Re S(r u) is at least Re u times the norm of S(r u).

**Definition 1.26 (Sector majorant).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.sectorMajorant`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.sectorMajorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q_kappa(r) is r (4 + r^2) / (4 (sqrt(kappa))^5 (sqrt(1 + r^2))^5).

**Theorem 1.27 (Pointwise radial potential bound).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.norm_radialQ_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.norm_radialQ_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa > 0, a unit ray with Re u at least kappa, and r > 0, the norm of q(r) is at most Q_kappa(r).

**Theorem 1.28 (Finite interval mass bound).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.sectorMajorant_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.sectorMajorant_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of real endpoints and kappa > 0, the oriented integral of Q_kappa is at most 1 / (2 (sqrt(kappa))^5). The negative derivative of ((1+r^2)^(-1/2) + (1+r^2)^(-3/2)) / (4 kappa^(5/2)) is Q_kappa.

**Theorem 1.29 (Terminal values of the decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.radial_K_terminal`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.radial_K_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As r tends to infinity along Re u > 0, F_K(r u) tends to one and (D F_K)(r u) tends to zero. In the reciprocal coordinate v = 1/w, write T = S(v). The principal-root and logarithm identities give the analytic amplitude sqrt(T) exp(nu (v/(1+T) - Log(v+T))) P_m(v/nu) at v = 0. The derivative in the phase variable acts there by multiplying the v derivative by -v^2/T.

**Definition 1.30 (Sector mass).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.sectorMass`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.sectorMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V_kappa is 1 / (2 (sqrt(kappa))^5).

**Theorem 1.31 (Volterra bounds on a unit ray).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.radial_K_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.radial_K_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa > 0, nu > V_kappa, Re u at least kappa, |u| = 1 and r > 0, the norms of F_K(r u) and F_K(r u) - 1 are bounded by nu / (nu - V_kappa) and V_kappa / (nu - V_kappa), respectively.

**Theorem 1.32 (Uniform sector error and nonvanishing).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.sector_K_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.sector_K_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa > 0 and nu at least 4 V_kappa, at every nonzero w with Re w at least kappa |w|, the norm of F_K(w) - 1 is at most 2 V_kappa / nu, which is at most 1/2, and K_m(nu w) is nonzero.

**Definition 1.33 (Normalized regular amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.F_I`

*Formalization.* `D5/S3/Analytic/HalfIntegerBessel.F_I` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

F_I is sqrt(2 pi nu) sqrt(S(w)) exp(-nu eta(w)) I_m(nu w). The first root is real and the second is principal complex.

**Theorem 1.34 (Relative amplitude normalization).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.F_I_div_F_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.F_I_div_F_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re w > 0 with K_m(nu w) nonzero, the ratio F_I / F_K equals pi exp(-2 nu eta(w)) I_m(nu w) / K_m(nu w).

**Theorem 1.35 (Carrier quotient at the origin).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.radial_I_div_K_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.radial_I_div_K_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re u > 0, I_m(nu r u) / K_m(nu r u) tends to zero as r decreases to zero. Reversing the degree-m carrier P_m gives B_m with B_m(0) nonzero. The analytic expression for the quotient near zero is (-1)^m (exp(2z) B_m(-z) / B_m(z) - 1) / pi at z = nu r u.

**Theorem 1.36 (Phase at the origin).**

Lean statement: `D5/S3/Analytic/HalfIntegerBessel.radial_eta_re_atBot`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBessel.radial_eta_re_atBot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a unit ray, Re eta(r u) tends to negative infinity as r decreases to zero. Its log(r) term diverges and the remaining terms are continuous at zero.

## References

- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.D`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.F_I`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.F_I_div_F_K`
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
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.norm_radialQ_le`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.order`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.prefactor`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.psi`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.radialP`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.radialQ`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.radialSystem_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.radial_I_div_K_zero`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.radial_K_bounds`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.radial_K_terminal`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.radial_S_re_ge`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.radial_eta_re_atBot`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.sectorMajorant`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.sectorMajorant_mass`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.sectorMass`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.sector_K_estimate`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.wronskian_KI`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBessel.wronskian_KL`
- Dependency: [D5/S3/Analytic/HalfIntegerBesselPolynomial](HalfIntegerBesselPolynomial.md)
