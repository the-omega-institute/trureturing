# Type-A Outer SLn Action

## Abstract

Type-A Outer SLn Action.

The actual type-A diagonal, field and graph outer action has a rank-independent finite-outer bound and a determinant-one normal form. It consumes inner-torus and finite ordered value blocks from PartII Sections2 and5.

**Definition 1.1 (boundaryTorus).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.boundaryTorus`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.boundaryTorus` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual D0: only the first and last diagonal coefficients may vary. It has no determinant-root or bounded-rank premise.

**Definition 1.2 (boundaryAction).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.boundaryAction`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.boundaryAction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual full determinant-one boundary diagonal/field/positive-graph action.

**Definition 1.3 (finiteOuter).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.finiteOuter`

*Formalization.* `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.finiteOuter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructed finite D0 Phi Gamma subgroup, with actual full SL actions. Inverses are derived from finite order of the concrete automorphism group, not from a supplied outer-subgroup premise.

**Theorem 1.4 (actual DFG finite outer normalization).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_DFG_finite_outer_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_DFG_finite_outer_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Actual determinant-one normalization of every prescribed DFG entry into constructed finiteOuter. The correcting matrix and complete action identity are produced before any targets. No bare automorphism classification is assumed or inferred from an agreement only on U.

**Theorem 1.5 (actual finite outer card).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_finite_outer_card`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_finite_outer_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual finite D0 Phi Gamma subgroup has a cardinality bound that is independent of rank. This deliberately uses the elementary |Aut(F)| bound |F|^|F|, without citing a cyclic-Galois theorem as an oracle.

**Theorem 1.6 (actual finite outer small field card).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_finite_outer_small_field_card`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_finite_outer_small_field_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rank-independent small-field bound, before any rank or action tuple. This is a genuine constructed subgroup bound, not a finite-outer premise.

**Theorem 1.7 (actual small field DFG commutator values).**

Lean statement: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_small_field_DFG_commutator_values`

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_small_field_DFG_commutator_values` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Concrete Section5 original DFG value consumer. The rank-independent outer subgroup, its cardinality and actual determinant-one normalization are constructed above. Only the fixed-root law is required here; no class width or full-group coverage is assumed. Corrections precede all genuine ordinary witnesses and the original q/e powers and order remain exact.

Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.

## References

- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_DFG_finite_outer_normalization`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_finite_outer_card`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_finite_outer_small_field_card`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.actual_small_field_DFG_commutator_values`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.boundaryAction`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.boundaryTorus`
- Truth anchor: `D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterSLnAction.finiteOuter`
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterBlockConstruction](PartIIOuterBlockConstruction.md)
- Dependency: [D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalInnerTorus](PartIIRadicalInnerTorus.md)
