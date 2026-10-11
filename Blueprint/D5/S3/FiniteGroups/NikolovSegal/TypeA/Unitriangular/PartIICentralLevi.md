# Type-A Central Levi

## Abstract

Type-A Central Levi.

Part II p255: actual central SL(n-2), with full diagonal actions implemented by determinant-one ambient inner corrections.

**Definition 1.1 (embed).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi.embed`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi.embed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The genuine central Levi embedding, fixing the first and last factors.

**Theorem 1.2 (actual central levi action).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi.actual_central_levi_action`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi.actual_central_levi_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full actual ambient field/graph/diagonal action intertwines with the central action, including inverse-transpose and its signs.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi.actual_central_levi_action`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi.embed`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus](PartIIRadicalInnerTorus.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks](SLnUnipotentBlocks.md)
