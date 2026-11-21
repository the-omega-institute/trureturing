# Sector bounds for the half-integer Bessel amplitudes

## Abstract

Radial integration controls the normalized decaying and regular amplitudes on right half-plane sectors.

**Theorem 1.1 (Evaluation of the reversed carrier).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.reverse_eval`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.reverse_eval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At nonzero z the reversed carrier evaluates to z^m times P_m(1/z).

**Definition 1.2 (Radial phase coefficient).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.radialP`

*Formalization.* `D5/S3/Analytic/HalfIntegerBesselSector.radialP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the ray r u, p(r) is S(r u) / r.

**Definition 1.3 (Radial potential coefficient).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.radialQ`

*Formalization.* `D5/S3/Analytic/HalfIntegerBesselSector.radialQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the ray, q(r) is p(r) psi(r u).

**Theorem 1.4 (Radial system for the decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.radialSystem_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.radialSystem_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re u > 0 and r > 0, eta(r u) has derivative p(r). With F(r) = F_K(r u) and G(r) = (D F_K)(r u), the real derivatives are F' = p G and G' = 2 nu p G + q F. Also Re p > 0.

**Theorem 1.5 (Sector angle of the phase root).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.radial_S_re_ge`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.radial_S_re_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If u has unit norm and positive real part and r > 0, then Re S(r u) is at least Re u times the norm of S(r u).

**Definition 1.6 (Sector majorant).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.sectorMajorant`

*Formalization.* `D5/S3/Analytic/HalfIntegerBesselSector.sectorMajorant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q_kappa(r) is r (4 + r^2) / (4 (sqrt(kappa))^5 (sqrt(1 + r^2))^5).

**Theorem 1.7 (Pointwise radial potential bound).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.norm_radialQ_le`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.norm_radialQ_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa > 0, a unit ray with Re u at least kappa, and r > 0, the norm of q(r) is at most Q_kappa(r).

**Theorem 1.8 (Finite interval mass bound).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.sectorMajorant_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.sectorMajorant_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every pair of real endpoints and kappa > 0, the oriented integral of Q_kappa is at most 1 / (2 (sqrt(kappa))^5). The negative derivative of ((1+r^2)^(-1/2) + (1+r^2)^(-3/2)) / (4 kappa^(5/2)) is Q_kappa.

**Theorem 1.9 (Terminal values of the decaying amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.radial_K_terminal`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.radial_K_terminal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

As r tends to infinity along Re u > 0, F_K(r u) tends to one and (D F_K)(r u) tends to zero. In the reciprocal coordinate v = 1/w, write T = S(v). The principal-root and logarithm identities give the analytic amplitude sqrt(T) exp(nu (v/(1+T) - Log(v+T))) P_m(v/nu) at v = 0. The derivative in the phase variable acts there by multiplying the v derivative by -v^2/T.

**Definition 1.10 (Sector mass).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.sectorMass`

*Formalization.* `D5/S3/Analytic/HalfIntegerBesselSector.sectorMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V_kappa is 1 / (2 (sqrt(kappa))^5).

**Theorem 1.11 (Volterra bounds on a unit ray).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.radial_K_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.radial_K_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa > 0, nu > V_kappa, Re u at least kappa, |u| = 1 and r > 0, the norms of F_K(r u) and F_K(r u) - 1 are bounded by nu / (nu - V_kappa) and V_kappa / (nu - V_kappa), respectively.

**Theorem 1.12 (Uniform sector error and nonvanishing).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.sector_K_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.sector_K_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa > 0 and nu at least 4 V_kappa, at every nonzero w with Re w at least kappa |w|, the norm of F_K(w) - 1 is at most 2 V_kappa / nu, which is at most 1/2, and K_m(nu w) is nonzero.

**Definition 1.13 (Normalized regular amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.F_I`

*Formalization.* `D5/S3/Analytic/HalfIntegerBesselSector.F_I` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

F_I is sqrt(2 pi nu) sqrt(S(w)) exp(-nu eta(w)) I_m(nu w). The first root is real and the second is principal complex.

**Theorem 1.14 (Relative amplitude normalization).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.F_I_div_F_K`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.F_I_div_F_K` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On Re w > 0 with K_m(nu w) nonzero, the ratio F_I / F_K equals pi exp(-2 nu eta(w)) I_m(nu w) / K_m(nu w).

**Theorem 1.15 (Carrier quotient at the origin).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.radial_I_div_K_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.radial_I_div_K_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For Re u > 0, I_m(nu r u) / K_m(nu r u) tends to zero as r decreases to zero. Reversing the degree-m carrier P_m gives B_m with B_m(0) nonzero. The analytic expression for the quotient near zero is (-1)^m (exp(2z) B_m(-z) / B_m(z) - 1) / pi at z = nu r u.

**Theorem 1.16 (Phase at the origin).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.radial_eta_re_atBot`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.radial_eta_re_atBot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a unit ray, Re eta(r u) tends to negative infinity as r decreases to zero. Its log(r) term diverges and the remaining terms are continuous at zero.

**Theorem 1.17 (Uniform sector bounds for the regular amplitude).**

Lean statement: `D5/S3/Analytic/HalfIntegerBesselSector.sector_I_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/HalfIntegerBesselSector.sector_I_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For kappa > 0 and nu at least 4 V_kappa, let delta = 2 V_kappa / nu. At every nonzero w with Re w at least kappa |w|, the norm of F_I(w)/F_K(w) - 1 is at most 10 delta / kappa, and the norm of F_I(w) - 1 is at most (1 + 15 / kappa) delta. Along the inward ray, the Wronskian gives the derivative of the normalized quotient correction as the phase kernel derivative times (F_K^(-2) - 1). Factoring the inverse square error bounds its norm by 10 delta. The sector angle compares the derivative norm to the derivative of the real exponential kernel. Finite interval integration and the zero limit of the correction at the origin give the quotient bound. Multiplying by F_K and using its norm bound of 3/2 gives the regular amplitude bound.

## References

- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.F_I`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.F_I_div_F_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.norm_radialQ_le`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.radialP`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.radialQ`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.radialSystem_K`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.radial_I_div_K_zero`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.radial_K_bounds`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.radial_K_terminal`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.radial_S_re_ge`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.radial_eta_re_atBot`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.reverse_eval`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.sectorMajorant`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.sectorMajorant_mass`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.sectorMass`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.sector_I_estimate`
- Truth anchor: `D5/S3/Analytic/HalfIntegerBesselSector.sector_K_estimate`
- Dependency: [D5/S3/Analytic/HalfIntegerBessel](HalfIntegerBessel.md)
- Dependency: [D5/S3/Analytic/HalfIntegerBesselPolynomial](HalfIntegerBesselPolynomial.md)
- Dependency: [D5/S3/Analytic/RadialVolterra](RadialVolterra.md)
