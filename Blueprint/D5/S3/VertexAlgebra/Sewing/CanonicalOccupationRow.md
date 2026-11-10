# Canonical occupation coordinates and row bounds

## Abstract

Literal occupation coordinates and private coefficient estimates consumed by canonical occupation sewing.

This companion supplies the literal occupation coordinates for CanonicalOccupation.canonical_sewing_summable. Every lattice D, integral charge and signed mode remains arbitrary; occupations have no cutoff.

**Definition 1.1 (Internal occupations).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.Occ`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.Occ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All finitely supported natural occupations on Fin D.rank times Nat.

**Definition 1.2 (Oscillator energy).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.level`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.level` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing positive integer oscillator energy, with frequency k+1 at index (i,k).

**Definition 1.3 (Literal monomial state).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.b`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The monomial with occupation d and coefficient one in the original oscillator polynomial carrier.

**Definition 1.4 (Creation occupation numerator).**

Lean statement: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.creationCoordinate`

*Formalization.* `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.creationCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite product of (alpha(i)/(k+1)) to the occupation multiplicity, obtained from the original creation exponential.

The private creation-coefficient proof differentiates the original creation exponential and identifies its exact factorial coordinate. The public LatticeActualProductKernel convolution and raw creator supply the actual creation-and-translation field. Both original normal-product branches, including the charge zero mode, yield a finite word-coefficient recurrence. Induction on the actual descendant word gives the uniform row envelope C(1+level(d))^K L^degree(d). CanonicalOccupation imports the private coefficient, recurrence and row helpers for its complementary column bound and final literal scalar contraction; no separate public estimate theorem is introduced.

The lattice-field and normal-product attributions remain those of the imported Bakalov--Kac, Matsuo--Nagatomo and Carnahan suppliers. Mathlib supplies polynomial derivatives and finite-support estimates. These coordinates and private estimates do not assert an invariant BPZ form, physical unitarity, operator convergence, channel reassociation or complete CFT sewing.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.Occ`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.b`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.creationCoordinate`
- Truth anchor: `D5/S3/VertexAlgebra/Sewing/CanonicalOccupationRow.level`
- Dependency: [D5/S3/Combinatorics/Partitions/AnalyticIntegerOccupation](../../Combinatorics/Partitions/AnalyticIntegerOccupation.md)
- Dependency: [D5/S3/VertexAlgebra/FactorialFockMetric](../FactorialFockMetric.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeActualAnnihilation](../LatticeActualAnnihilation.md)
- Dependency: [D5/S3/VertexAlgebra/LatticePositiveEnergy](../LatticePositiveEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeSectorIntertwiner](../Sectors/LatticeSectorIntertwiner.md)
