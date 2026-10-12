# Type-A Radical Inner Torus

## Abstract

Type-A Radical Inner Torus.

**Theorem 1.1 (actual diagonal inner normalization).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.actual_diagonal_inner_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.actual_diagonal_inner_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant equality is exactly the inner-correction obstruction. The actual determinant-one matrix is constructed and its FULL action is proved for every field/graph tuple, before any coordinate targets.

**Definition 1.2 (radicalDiagonal).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.radicalDiagonal`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.radicalDiagonal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual p263 diagonal pattern. Its two exceptional entries absorb all prescribed determinant obstruction; the length of the middle block has no effect on the scalar exponent.

**Theorem 1.3 (actual radical inner torus).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.actual_radical_inner_torus`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.actual_radical_inner_torus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact determinant-one INNER correction construction used by PartII Proposition6.7, p263. This consumes the actual determinant and full automorphism laws above, and leaves no supplied diagonal-normalization premise. The middle tuple is genuinely constant, even in unbounded rank. It is the correction step, not radical value coverage.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.actual_diagonal_inner_normalization`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.actual_radical_inner_torus`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus.radicalDiagonal`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIPropositionSixFive](PartIIPropositionSixFive.md)
