# SixSupportLaplacianPolynomial

## Abstract

Exact polynomial identities for the actual six-support quotient.

**Theorem 1.1 (Zero factor).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianPolynomial.charpoly_zero_factor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianPolynomial.charpoly_zero_factor` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

Over every commutative coefficient ring, the characteristic polynomial of the literal six-cell matrix is X times its reduced characteristic polynomial. The zero eigenvalue is removed exactly once as a polynomial factor; no nonzero root or multiplicity is silently discarded.

**Theorem 1.2 (Division-free determinant).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianPolynomial.determinant_formula`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianPolynomial.determinant_formula` (`✓ std3`). ∎

*Citation.* the-omega-institute/ideal-intersection-laplacian contributors (2026). *Six-support complement quotient, global endpoint spectrum, fixed-gap expansion and integer finiteness*. URL: <https://github.com/the-omega-institute/ideal-intersection-laplacian/blob/b93becea662a746badeadba42fdc3d3eb3db9382/paper/core/body.tex>.

*Commentary.*

For all parameters and every commutative ring, the actual six-by-six determinant equals the full three-factor expression with all mixed correction terms. The proof uses the literal matrix and exact minors. Specializations, arithmetic restrictions and actual graph eigenvalue transport are separate consumers.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianPolynomial.charpoly_zero_factor`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianPolynomial.determinant_formula`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/SixSupportLaplacianLowRoot](SixSupportLaplacianLowRoot.md)
- Dependency: [D5/S3/Combinatorics/SpectralGraph/SixSupportQuadraticTower](SixSupportQuadraticTower.md)
