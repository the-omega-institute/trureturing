# Type-A SLn Unitriangular Card

## Abstract

Type-A SLn Unitriangular Card.

An actual entry-coordinate bijection for the full upper unitriangular subgroup, over every field and rank.

**Definition 1.1 (UpperEntry).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.UpperEntry`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.UpperEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

One free coordinate for each entry strictly above the diagonal.

**Definition 1.2 (upperMatrix).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperMatrix`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal unitriangular matrix with the prescribed free upper entries.

**Definition 1.3 (upperChart).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperChart`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every assignment of free entries is an actual determinant-one Uplus element.

**Definition 1.4 (upperCoordinatesEquiv).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperCoordinatesEquiv`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperCoordinatesEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual coordinate equivalence, not a group-order or coverage hypothesis.

**Theorem 1.5 (card Uplus sum).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.card_Uplus_sum`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.card_Uplus_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact cardinality as the sum of column dimensions, valid also in ranks0/1.

**Theorem 1.6 (card Uplus).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.card_Uplus`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.card_Uplus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal free-entry dimension n*(n-1)/2.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.UpperEntry`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.card_Uplus`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.card_Uplus_sum`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperChart`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperCoordinatesEquiv`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangularCard.upperMatrix`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnitriangular](SLnUnitriangular.md)
