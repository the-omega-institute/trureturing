# Type-A SLn Unipotent Reduction

## Abstract

Type-A SLn Unipotent Reduction.

**Theorem 1.1 (prepare last row).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentReduction.prepare_last_row`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentReduction.prepare_last_row` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One actual lower-radical operation supplies a nonzero earlier entry in the last row. The only input is the genuine nonzero row of an SL matrix.

**Theorem 1.2 (rank reduction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentReduction.rank_reduction`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentReduction.rank_reduction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual determinant-one rank reduction, with exactly four radical positions. There is no pivot, flag, cardinality or decomposition premise.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentReduction.prepare_last_row`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentReduction.rank_reduction`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks](SLnUnipotentBlocks.md)
