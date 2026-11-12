# Actual residue degree and f units at finite D places

## Abstract

Actual residue degree and f units at finite D places

Let k be a characteristic-zero field and let K=k(b). The quadratic field H=K(sqrt(D)) and the further quadratic field F=H(sqrt(f)) use the fixed polynomials of the six-support equality curve. The finite places considered here lie above roots of D on the affine b-line. Their normalized multiplicative valuations, residue fields and ramification indices refer to the actual integral closure and its prime localizations.

**Theorem 1.1 (Residue degree one).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.residue_degree_one`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.residue_degree_one` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The actual residue field of every D-root prime is k, with library inertia degree1.

**Theorem 1.2 (The actual f has a local unit representative).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.localF_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.localF_unit` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The local numerator and denominator are units at every actual D root; the local representative maps to the same supplied f in H.

**Theorem 1.3 (The local representative maps to the actual f).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.localF_intoH`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.localF_intoH` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

The map is the fixed actual localization embedding into H, with its prescribed algebra structure.

**Theorem 1.4 (Every actual finite D place gives valuation one).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.valuation_f`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.valuation_f` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Multiplicative normalized valuation of f is1, equivalently additive order zero.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.localF_intoH`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.localF_unit`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.residue_degree_one`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootUnits.valuation_f`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/SixSupportFiniteRootGeometry](SixSupportFiniteRootGeometry.md)
