# Central residues of the diagonal exponential Padé denominator

## Abstract

The reflected finite carrier determines the normalized residues at central Padé poles.

**Definition 1.1 (Decaying amplitude logarithm).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.residueAmplitudeLog`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.residueAmplitudeLog` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The logarithm is Log F_K − (Log S)/2, with the principal logarithms of the decaying amplitude F_K and of S(w) = sqrt(1+w²).

**Definition 1.2 (Centered residue logarithm).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.normalizedResidueLog`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.normalizedResidueLog` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

With Δ denoting the difference from a reference scaled pole, the exponent is −ν ΔLog w + ν Δw − ν Δη + Δ residueAmplitudeLog.

**Theorem 1.3 (Exact reflected residue ratio).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exp_normalizedResidueLog`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exp_normalizedResidueLog` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For two odd-order poles 2νw and 2νw₀, both scaled arguments have positive real part and nonzero decaying amplitudes. Exponentiating the centered logarithm gives R(2νw)/R(2νw₀). Reflecting the reversed denominator cancels the alternating sign. The geometric residue uses the scale z^(2m+1), giving the centered power term −ν ΔLog w.

**Definition 1.4 (Pole at an integer phase).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.centralPole`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.centralPole` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

The pole of index j for the inverse g is 2ν g(j π i/ν).

**Definition 1.5 (Exponent for a normalized summand).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.centralSummandExponent`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.centralSummandExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For coefficient index n the summand exponent is the centered residue logarithm minus n times the centered pole logarithm.

**Definition 1.6 (Gaussian exponent and signed phase).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.gaussianSummandExponent`

*Formalization.* `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.gaussianSummandExponent` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

Write 1/a = c/sqrt(1+c²), b = 1/sqrt(1+c²), D = c²/(2(1+c²)²), and τ = n/ν². The exponent is −π² D τ j² + i j θ, where θ = π(1/a−b−1) − π b n/ν.

**Theorem 1.7 (Uniform central residue comparison).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exists_central_residue_comparison`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exists_central_residue_comparison` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

At a positive zero c of η, a common cutoff and order threshold give distinct central poles for all sufficiently large odd m. They include every pole whose scaled argument lies in a fixed neighborhood of c. The index-zero pole r and its residue W are positive real numbers. The centered residue logarithm is analytic on the closed cutoff disk. Throughout the disk it differs from ν(1/a−b−1)s by at most A(ν|s|²+|s|), and at s = j π i/ν its exponential is the exact residue ratio. The corrected-phase derivative and the amplitude logarithm on fixed disks control the error. For all n with τ in [1/4,1/2], the exact normalized pole summand has an exponent which differs from the Gaussian exponent by at most B(|j|+j²+|j|³)/ν. Every fixed finite range of indices is included above a threshold independent of n. The same pointwise error bounds the complex summands after exponentiation, since the exact and Gaussian exponents lie in the closed left half-plane.

**Theorem 1.8 (Uniform finite-sum comparison).**

Lean statement: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exists_uniform_central_residue_truncation`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exists_uniform_central_residue_truncation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* NIST Digital Library of Mathematical Functions (2010). *DLMF 10.17.1 and 10.49, coefficients of the finite half-integer Bessel expansions*. URL: <https://dlmf.nist.gov/10.17.E1>.

*Commentary.*

For each fixed J there is a common order threshold for every n in the closed window and every finite set of integer indices with |j| ≤ J. The set indexes distinct actual poles and uses the positive central normalization W r⁻ⁿ. The norm of the difference between the two finite sums is at most B times the number of indices divided by ν, where B depends on c and J.

## References

- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.centralPole`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.centralSummandExponent`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exists_central_residue_comparison`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exists_uniform_central_residue_truncation`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.exp_normalizedResidueLog`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.gaussianSummandExponent`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.normalizedResidueLog`
- Truth anchor: `D5/S3/Analytic/Polynomial/DiagonalPadeResidue.residueAmplitudeLog`
- Dependency: [D5/S3/Analytic/HalfIntegerBessel](../HalfIntegerBessel.md)
- Dependency: [D5/S3/Analytic/HalfIntegerBesselSector](../HalfIntegerBesselSector.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeCentralPoles](DiagonalPadeCentralPoles.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadeExponential](DiagonalPadeExponential.md)
- Dependency: [D5/S3/Analytic/Polynomial/DiagonalPadePhase](DiagonalPadePhase.md)
