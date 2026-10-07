# Cellular Solidification

## Abstract

A concrete unbounded cellular construction from the protected defining maps. Each step attaches mapping cones along every chain map from every integer placement of a defining cell. The proved null-homotopies below are actual data. The sequential colimit is a construction in complexes; locality and the derived universal property are not claimed here.

**Definition 1.1 (solid Cellular Colimit).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/CellularSolidification.solidCellularColimit`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/CellularSolidification.solidCellularColimit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual sequential colimit, formed degreewise, of all cellular stages. This definition alone asserts neither locality nor a derived adjunction.

**Definition 1.2 (solid Cellular Colimit Homotopy).**

Lean statement: `D5/S3/HomologicalAlgebra/Solid/CellularSolidification.solidCellularColimitHomotopy`

*Formalization.* `D5/S3/HomologicalAlgebra/Solid/CellularSolidification.solidCellularColimitHomotopy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maps from defining cells that enter at any finite stage are explicitly null-homotopic in the full sequential colimit.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/CellularSolidification.solidCellularColimit`
- Truth anchor: `D5/S3/HomologicalAlgebra/Solid/CellularSolidification.solidCellularColimitHomotopy`
- Dependency: [D5/S3/HomologicalAlgebra/Solid/LocalizationDefect](LocalizationDefect.md)
