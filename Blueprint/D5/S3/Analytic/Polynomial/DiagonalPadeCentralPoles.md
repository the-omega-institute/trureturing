# Central poles of the diagonal exponential Padé denominator

## Abstract

The analytic phase inverse indexes the central poles and controls their radial growth.

**Theorem 1.1 (Modulus of a lattice value).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeCentralPoles.norm_polePhaseLattice`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeCentralPoles.norm_polePhaseLattice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The modulus of the phase value at integer index j is |j| π/ν.

**Theorem 1.2 (Central poles and uniform estimates).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeCentralPoles.exists_central_poles`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeCentralPoles.exists_central_poles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

About every positive zero c of η there are fixed radii 0 < ε ≤ r ≤ c/4 and 0 < t₀ < ρ, positive constants B and C, and an order threshold. Above it, the corrected phase at odd orders has an analytic inverse g_m on the open disk of radius ρ. Its values lie in the open disk of radius r about c, it commutes with conjugation and its value at zero is positive real and within B/ν² of c. For every |j| π/ν ≤ t₀ there is a distinct pole at 2ν g_m(j π i/ν). This list includes every root whose scaled argument lies in the open disk of radius ε about c. Every fixed finite range of integer indices lies within the cutoff for all sufficiently large orders. For real |t| ≤ t₀, log(|g_m(it)|/|g_m(0)|) is at least c² t²/(4(1+c²)²). The derivative of the limiting log inverse is 1/S(g(s)) and its second derivative at zero is −c²/(1+c²)². Cauchy's estimate transfers the curvature to the corrected inverse. Write a = sqrt(1+c²)/c, b = 1/sqrt(1+c²) and D = c²/(2(1+c²)²). For complex |s| ≤ t₀, g_m(s)−g_m(0) differs from s/a by at most C(|s|/ν²+|s|²), and Log g_m(s)−Log g_m(0) differs from bs−Ds² by at most C(|s|/ν²+|s|³).

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeCentralPoles.exists_central_poles`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeCentralPoles.norm_polePhaseLattice`
- Dependency: [D5/S3/Analytic/HalfIntegerBessel](../HalfIntegerBessel.md)
- Dependency: [D5/S3/Analytic/HalfIntegerBesselSector](../HalfIntegerBesselSector.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeExponential](DiagonalPadeExponential.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadePhase](DiagonalPadePhase.md)
