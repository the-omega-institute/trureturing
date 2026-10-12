# Type-A Radical Coordinates

## Abstract

Type-A Radical Coordinates.

Actual radical of the first-row/last-column parabolic, Part II pp262–263. The corner is retained, including its ordered cross term.

**Definition 1.1 (radical).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.radical`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.radical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Genuine determinant-one radical matrix with all three coordinates.

**Theorem 1.2 (actual radical mul).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_mul`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact noncommutative radical multiplication: only the first row of THE LEFT factor pairs with the last column of THE RIGHT factor.

**Theorem 1.3 (actual radical inverse).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_inverse`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual inverse, including the central quadratic correction.

**Definition 1.4 (InRadical).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.InRadical`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.InRadical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal first-row/last-column subgroup predicate, with genuine unitriangularity. This is not an abstract coverage assumption.

**Theorem 1.5 (actual radical coordinates).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual radical target has these genuine matrix coordinates.

**Theorem 1.6 (actual radical row).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_row`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual noncorner first-row coordinate.

**Theorem 1.7 (actual radical product mem).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_product_mem`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_product_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Closure is proved for the literal matrix support, not postulated.

**Theorem 1.8 (actual radical product row column).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_product_row_column`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_product_row_column` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact additive quotient coordinates, while the corner still uses actual_radical_mul's noncommutative cross term.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.InRadical`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_coordinates`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_inverse`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_mul`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_product_mem`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_product_row_column`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.actual_radical_row`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCoordinates.radical`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus](PartIIRadicalInnerTorus.md)
