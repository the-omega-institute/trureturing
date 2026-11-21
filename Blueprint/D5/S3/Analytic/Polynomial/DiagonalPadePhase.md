# Central phase of the diagonal exponential Padé denominator

## Abstract

The corrected analytic phase quantizes the central poles of the odd diagonal Padé denominator.

**Theorem 1.1 (Simple positive zero of the limiting phase).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.exists_eta_positive_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadePhase.exists_eta_positive_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The native Liouville–Green phase has a unique positive real zero c in (0, 1). Its complex derivative at c is sqrt(1+c²)/c. On the positive line the phase increases strictly, tends to minus infinity at zero, and is positive at one.

**Definition 1.2 (Corrected phase).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

With ν = m + 1/2, the phase Φ_m is η + Log(F_I/F_K)/(2ν). The logarithm is the principal complex logarithm.

**Theorem 1.3 (Analyticity and sector bound).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase_sector`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase_sector` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For 0 < κ ≤ 1 and ν ≥ 40 V_κ/κ, both amplitudes are nonzero in the open sector κ |w| < Re w. The ratio has strictly positive real part and the phase is analytic there. The phase differs from η by at most 15 V_κ/(κν²).

**Definition 1.4 (Integer phase value).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhaseLattice`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhaseLattice` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The phase value of index j is j π i/ν.

**Theorem 1.5 (Exact odd-order phase lattice).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.denominator_zero_iff_polePhase`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadePhase.denominator_zero_iff_polePhase` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For odd m with the same sector and order conditions, q_m(2ν w) vanishes exactly when Φ_m(w) = j π i/ν for an integer j. Exponentiating the corrected phase gives π I_m(ν w)/K_m(ν w), whose equality to one is the vanishing condition.

**Theorem 1.6 (Uniform perturbation on nested disks).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase_compact_estimate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase_compact_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For positive c and ν ≥ 160 V_(1/4), the phase error is at most 60 V_(1/4)/ν² on the closed disk of radius c/2 about c. Its derivative is bounded by 240 V_(1/4)/(cν²) on the closed disk of radius c/4. The larger disk lies inside the open sector and a circle of radius c/4 about each point of the smaller disk gives the Cauchy estimate.

**Theorem 1.7 (Uniform inverse on a fixed disk).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.exists_uniform_polePhase_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadePhase.exists_uniform_polePhase_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

At a positive real zero c of η, there are fixed positive radii r ≤ c/4 and ρ and a constant B > 0. For all sufficiently large orders, with threshold at least 160 V_(1/4) in ν, η and Φ_m have analytic inverses g and g_m on the open disk of radius ρ about zero. Their values lie in the open disk of radius r about c, and each is the unique solution in the corresponding closed disk. Throughout the inverse disk, |g_m-g| ≤ B/ν². A uniform affine derivative estimate gives a contraction on the closed disk and the local inverse theorem establishes analyticity.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.denominator_zero_iff_polePhase`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.exists_eta_positive_zero`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.exists_uniform_polePhase_inverse`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhaseLattice`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase_compact_estimate`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadePhase.polePhase_sector`
- Dependency: [D5/S3/Analytic/HalfIntegerBessel](../HalfIntegerBessel.md)
- Dependency: [D5/S3/Analytic/HalfIntegerBesselSector](../HalfIntegerBesselSector.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeExponential](DiagonalPadeExponential.md)
